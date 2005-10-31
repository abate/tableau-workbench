
open Llist
open Tree
open Data
open Datatype

let newcontext = RuleContext.newcontext
let match_node = Partition.match_node
let build_node = Build.build_node

let rec branchcond context tl tLl bll =
    let treelist = 
        match tLl with
        |Empty -> tl
        | _ -> (Llist.hd tLl)::tl in
    let checknext cxt tl = function
        |[] -> true
        |bl -> 
            let (_, sbl, node) = context#get in
            let (_, hist, _) = node#get in
            let varlist = 
                List.map ( function
                    |Leaf(n) -> let (_,_,v) = n#get in v 
                    |_ -> failwith "check_branch_cond"
                ) tl
            in
            List.for_all ( fun f -> f sbl hist varlist ) bl
    in
    (* we have to check tLl to take into account implicit backtracking *)
    match bll,tLl with
    |[],Empty -> List.rev treelist
    |[],_ -> branchcond context treelist (Llist.tl tLl) []
    |[]::btl,_ -> branchcond context treelist (Llist.tl tLl) btl
    |hd::btl,_ when (checknext context treelist hd) ->
            (* Llist.tl forces the computation of the next node. if
            * the branch condition fails, the next node is not explored *)
            branchcond context treelist (Llist.tl tLl) btl
    |_ -> List.rev treelist
;;

let status s 
(sbl : NodePattern.sbl)
(hist : History.store)
(varlist : Variable.store list ) =
    let varhist = 
        try List.nth varlist ((List.length varlist) - 1)
        with Failure "nth" -> failwith "status: nth"
    in
    try
        (match varhist#find "status" with
        `Set l -> 
            (match l#elements with
            |[`String str] when s = str -> true
            |[`String _] -> false
            |[] -> true
            |_ -> failwith "status: elements")
        |_ -> failwith "custom status: type mistmatch")
    with Not_found -> failwith "custom status: not found"
;;

let is_open = status "Open";;
let is_closed = status "Closed";;

(* check method for any rule *)
let check node patternl historyl =
    let match_all node (pl, sl) hl =
        let (map, hist, varhist) = node#get in
        (* principal formulae and sets enumeration *)
        let enum = match_node map (pl, sl) in
        let (enum, sbl, newmap) =
            let rec check_hist e =
                (* here I filter the enum wrt the side conditions *)
                let filtered_enum =
                    Enum.filter (function sbl, ns ->
                            not(List.exists (
                                    fun c -> not (c sbl hist [varhist])
                                ) hl
                            )
                    ) e
                in
                (* now filtered_enum contains only the enum that
                 * respect the side conditions and I can build with
                 * it the new context for the rule *)
                try begin
                    match Enum.get filtered_enum with
                    |Some (sbl, ns) -> (filtered_enum, sbl, ns)
                    |None -> raise Partition.FailedMatch (* no more choices *)
                end with Partition.FailedMatch ->
                    (Enum.empty (), Data.Substlist.empty, map)
           in check_hist enum
       in
       let newnode = node#set (newmap, hist, varhist) in
       newcontext (enum, sbl, newnode)
    in match_all node patternl historyl
;;

let nodeid = ref 0;;
let printer n name ruleid =
    let _ = incr nodeid in
    OutputBroker.print n name ruleid !nodeid
;;

(* down method for a rule with explicit branching *)
let down_explicit name context makelist =
  (* this is the rule application identifier *)
  let ruleid = !nodeid in
  let action_all node sbl oldvar al hl =
    let (map, hist, varhist) = node#get in
    let newmap = build_node map sbl hist oldvar al in
    let newhist =
        List.fold_left (fun h f ->
            let (k,v) = f sbl h oldvar in
            h#add k v
        ) hist hl
    in
    let n = node#set (newmap, newhist, varhist) in
    let _ = printer n name ruleid in n
  in
  let rec make_llist sbl oldvar =
    function
      [] -> Empty
    | (node, al, hl) :: t ->
            let next = action_all node sbl oldvar al hl in
            let (_, _, nextvar) = next#get in
            LList (next, lazy (make_llist sbl (nextvar::oldvar) t))
  in
  let (_, sbl, newnode) = context#get in
  Tree (make_llist sbl [Variable.make ()] (makelist newnode))
;;

(* down method for a rule with implicit branching *)
let down_implicit name context actionl historyl =
  (* this is the rule application identifier *)
  let ruleid = !nodeid in
  let action_all node sbl oldvar al hl =
    let (map, hist, varhist) = node#get in
    let newmap = build_node map sbl hist oldvar al in
    let newhist =
        List.fold_left (fun h f ->
            let (k,v) = f sbl h oldvar in
            h#add k v
        ) hist hl
    in
    let n = node#set (newmap, newhist, varhist) in
    let _ = printer n name ruleid in n
  in
  let rec make_llist oldvar =
    function
      Empty -> Empty
    | LList ((node, sbl, al, hl), t) ->
            let next = action_all node sbl oldvar al hl in
            let (_, _,nextvar) = next#get in
            LList (next, lazy (make_llist (nextvar::oldvar) (Lazy.force t)))
  in
  (* here we dynamically (lazily) generate the tail of the action list *)
  let rec next context =
    let (enum, sbl, node) = context#get in
    let (map, hist, vars) = node#get in
    let (newsbl, newmap) =
        (* enum is carefully constructed in check to
         * take side conditions into account and since
         * it is a lazy data structure, the conditions
         * are computed only when needed. Enum.get force
         * the computation *)
      match Enum.get enum with
        Some (sbl, ns) -> sbl, ns
      | None -> Data.Substlist.empty, map
    in
    if Data.Substlist.is_empty newsbl then
        LList ((node, sbl, actionl, historyl), lazy Empty)
    else
        let newnode = node#set (map, hist, vars) in
        LList ((node, sbl, actionl, historyl),
           lazy (next (context#set (enum, newsbl, newnode))))
  in
  Tree (make_llist [Variable.make ()] (next context))
;;

let down_axiom name context status =
    let (enum,sbl,newnode) = context#get in
    let (m, h, varhist) = newnode#get in
    let newnode = newnode#set(m#empty, h#empty, status varhist) in
    let _ = printer newnode name !nodeid in 
    Leaf(newnode)
;;

let unbox_tree = function
    Leaf (n) -> n
    |_ -> failwith "unbox_tree"
;;

(* up method - simple. explore the first branch, if the
 * branch condition is true, then explore the second branch. 
 * On backtrack apply a synth action, but the status is set
 * accrding the the branch condition *)
let up_explore_simple context treelist synthlist branchll =
    let (_, sbl, node) = context#get in
    let (_, hist, _) = node#get in
    (* tl holds the results of all branches that have been explored *)
    let tl = (branchcond context [] treelist branchll) in
    let varlist = 
        List.map ( function
            |Leaf(n) -> let (_,_,v) = n#get in v 
            |_ -> failwith "up_explore_simple"
        ) tl
    in
    let newnode =
        List.fold_left (
            fun n f ->
                (* here the function f return the variable
                 * history (sythethized histories) *)
                let (k,v) = f sbl hist varlist in
                let (m,h,var) = n#get in
                n#set (m,h,var#add k v)
        ) (unbox_tree (List.hd (List.rev tl))) synthlist
        (* XXX: hackish .... is it always the case the the last node has
         * the correct status ? *)
    in Leaf (newnode)
;;

let up_explore_linear context treelist synthlist =
    let (_, sbl, node) = context#get in
    let (_, hist, _) = node#get in
    let t = List.hd (Llist.to_list treelist) in
    let varhist =
        let n = unbox_tree t in
        let (_,_,v) = n#get in v
    in
    let newnode =
        List.fold_left (
            fun n f ->
                let (k,v) = f sbl hist [varhist] in
                let (m,h,var) = n#get in
                n#set (m,h,var#add k v)
        ) (unbox_tree t) synthlist
    in Leaf (newnode)
;; 
