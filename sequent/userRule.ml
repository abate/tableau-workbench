
open Llist
open Tree
open Data
open Datatype

let newcontext   = RuleContext.newcontext
let build_node   = Build.build_node
let build_sbl () = new Substitution.substitution

(* XXX: HACK this is a 'user' option that is set by the main program *)
let nodeid = ref 0;;

let printer n name ruleid =
    let _ = incr nodeid in
    OutputBroker.print n name ruleid !nodeid
;;


let rec branchcond ?(implicit=false) context acctl tLl bll =
    let treelist = 
        try (Llist.hd tLl)::acctl
        with Llist.LListEmpty -> acctl
    in
    let checknext cxt tl = function
        |[] -> true
        |bl -> 
            let (_, sbl, node) = context#get in
            let (_, hist, _) = node#get in
            let varlist = 
                List.map ( function
                    |Leaf(n) -> let (_,_,v) = n#get in v 
                    |_ -> failwith "check_branch_cond"
                ) (List.rev tl)
                (* I've to revert the list as this is the result of
                 * the accumulator acctl plus the last explored branch *)
            in
            List.for_all ( fun f -> f sbl hist varlist ) bl
    in
    (* we have to check tLl to take into account implicit backtracking. 
     * Llist.tl forces the computation of the next node. if the branch 
     * condition fails, the next node is not explored *)
    match bll,Lazy.force(tLl) with
    (* if it's empty there is nothing to do *)
    |_,Empty -> List.rev treelist
    (* if there are no conditions, the rule cannot be implicit.
     * Since is cannot be empty, we explore the next branch. *)
    |[],_ when implicit = false ->
            branchcond ~implicit:false context treelist (Llist.tl tLl) []
    (* if it is implicit, then it can have only one condition. If the
     * condition holds, then we explore the next branch MAINTAINIG the same
     * condition *)
    |hd::[],_ when implicit = true && (checknext context treelist hd) ->
             branchcond ~implicit:true context treelist (Llist.tl tLl) bll
    (* there is no condition on this branch, but maybe on others. We explore
     * the next branch without further checks and we pass the rest of the
     * condition list *)
    |[]::btl,_ when implicit = false ->
            branchcond ~implicit:false context treelist (Llist.tl tLl) btl
    (* if the condition is true then we explore the next branch passing the rest
     * of the condition list *)
    |hd::btl,_ when implicit = false && (checknext context treelist hd) ->
            branchcond ~implicit:false context treelist (Llist.tl tLl) btl
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
        `Singleton l -> 
            (match l#elements with
            |[`String str] when s = str -> true
            |[`String _] -> false
            |[] -> true
            |_ -> failwith "status: elements")
        |_ -> failwith "custom status: type mistmatch")
    with Not_found -> failwith "custom status: not found"
;;

let is_open = status "Open";;
let is_closed = status "Close";;

(* check method for any rule *)
let check name node patternl historyl =
    (* Printf.printf "check %s\n" name ; *)
    let match_all node (plzero, plone, sl) hl =
        let (map, hist, varhist) = node#get in
        (* principal formulae and sets enumeration *)
        let enum =
            match plzero,plone with
            |[],[] -> Partition.match_node_set (build_sbl (),map) sl
            |[],pl1 -> Partition.match_node_one (build_sbl (),map) (pl1, sl)
            |pl0,[] -> Partition.match_node_zero (build_sbl (),map) (pl0, sl)
            |pl0,pl1 -> Partition.match_node_trail (build_sbl (),map) (pl0,pl1, sl)
        in
        let (enum, sbl, newmap) =
            let rec check_hist e =
                (* here I filter the enum wrt the side conditions 
                 * and I discard enum that have empty sbl *)
                let filtered_enum =
                    Enum.filter (function (sbl,ns) ->
                        if not(sbl#is_empty) then
                            not(List.exists (
                                fun c -> not (c sbl hist [varhist])
                                ) hl
                            )
                        else false
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
                    (Enum.empty (), build_sbl (), map)
           in check_hist enum
       in
       let newnode = node#set (newmap, hist, varhist) in
       newcontext (enum, sbl, newnode)
    in match_all node patternl historyl
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
  let rec make_llist sbl oldvar = function
      |[] -> Llist.empty
      | (node, al, hl) :: t ->
              Llist.bind
              (Llist.return (lazy(action_all node sbl oldvar al hl))) (fun next ->
                  let (_, _, nextvar) = (Lazy.force(next))#get in
                  Llist.push (Lazy.force(next)) (make_llist sbl (nextvar::oldvar) t)
              )
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
  let rec make_llist oldvar l =
      match Lazy.force l with
      |Empty -> Llist.empty
      |LList ((node, sbl, al, hl), t) ->
              Llist.bind
              (Llist.return (lazy(action_all node sbl oldvar al hl))) (fun next ->
                  let (_, _,nextvar) = (Lazy.force(next))#get in
                  Llist.push (Lazy.force(next)) (make_llist (nextvar::oldvar) t)
              )
  in
  (* here we dynamically (lazily) generate the tail of the action list *)
  let rec next context =
    let (enum, sbl, node) = context#get in
    let (map, hist, vars) = node#get in
    let (newsbl, newmap) =
      (* enum is carefully constructed to take side conditions into account.
       * Since it is a lazy data structure, the conditions are computed only
       * when needed. Enum.get force the computation *)
      match Enum.get enum with
      |Some (sbl, ns) -> (sbl, ns)
      |None -> (build_sbl (), map)
    in
    if newsbl#is_empty then
        Llist.return (node, sbl, actionl, historyl)
    else
        let newnode = node#set (map, hist, vars) in
        Llist.push
        (node, sbl, actionl, historyl)
        (next (context#set (enum, newsbl, newnode)))
  in
  Tree (make_llist [Variable.make ()] (next context))
;;

let down_axiom name context arglist =
    let status = List.hd arglist in
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
 * On backtrack apply a synth action. *)
let up_explore_aux ?(implicit=false) context treelist synthlist branchll =
    let (_, sbl, node) = context#get in
    let (_, hist, _) = node#get in
    (* tl holds the results of all branches that have been explored *)
    (* since the list is lazy, the computation is triggered here *)
    let tl = (branchcond ~implicit:implicit context [] treelist branchll) in
    let t = match List.rev tl with
        |[] -> failwith "up_explore_aux : t"
        |h::_ -> h
    in
    let varlist = 
        List.map ( function
            |Leaf(n) -> let (_,_,v) = n#get in v 
            |_ -> failwith "up_explore_aux : varlist"
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
        ) (unbox_tree t) synthlist
        (* XXX: hackish .... is it always the case the the last node has
         * the correct status ? *)
    in Leaf (newnode)
;;

let up_explore_implicit context treelist synthlist branchll =
    up_explore_aux ~implicit:true context treelist synthlist branchll
let up_explore_simple context treelist synthlist branchll =
    up_explore_aux ~implicit:false context treelist synthlist branchll

let up_explore_linear context treelist synthlist =
    let (_, sbl, node) = context#get in
    let (_, hist, _) = node#get in
    let tl = (Llist.to_list treelist) in
    let t = match tl with
        |[] -> failwith "up_explore_linear : t"
        |h::_ -> h
    in
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

module ExtList = struct

    exception Different_list_size of string
    let map1 = List.map
    let map2 f (l1,l2) =
        let rec _aux acc = function
            |h1::t1,h2::t2 -> _aux (f (h1,h2)::acc) (t1,t2)
            |[],[] -> List.rev acc
            |_ -> raise (Different_list_size "map3")
        in _aux [] (l1,l2)
    ;;

    let map3 f (l1,l2,l3) =
        let rec _aux acc = function
            |h1::t1,h2::t2,h3::t3 -> _aux (f (h1,h2,h3)::acc) (t1,t2,t3)
            |[],[],[] -> List.rev acc
            |_ -> raise (Different_list_size "map3")
        in _aux [] (l1,l2,l3)
    ;;
    let map4 f (l1,l2,l3,l4) =
        let rec _aux acc = function
            |h1::t1,h2::t2,h3::t3,h4::t4 -> _aux (f (h1,h2,h3,h4)::acc) (t1,t2,t3,t4)
            |[],[],[],[] -> List.rev acc
            |_ -> raise (Different_list_size "map4")
        in _aux [] (l1,l2,l3,l4)
    ;;
    let map5 f (l1,l2,l3,l4,l5) =
        let rec _aux acc = function
            |h1::t1,h2::t2,h3::t3,h4::t4,h5::t5 ->
                    _aux (f (h1,h2,h3,h4,h5)::acc) (t1,t2,t3,t4,t5)
            |[],[],[],[],[] -> List.rev acc
            |_ -> raise (Different_list_size "map5")
        in _aux [] (l1,l2,l3,l4,l5)
    ;;

    let fold f l s =
        let n = List.length s in
        let rec def acc = function
            |0 -> acc
            |i -> def ([]::acc) (i-1)
        in
        let r = List.fold_left (fun l el ->
            let rl = f el in List.map2 (fun r l -> r::l) rl l
            ) (def [] n) l
        in List.combine s r
    ;;
end

