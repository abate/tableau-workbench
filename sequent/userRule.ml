
open Llist
open Tree
open Data

module Make (T:Data.S) (N:Node.S) (C: sig type t end) =
    struct

        type t = T.t
        type context_type = C.t
        type context = context_type Rule.ct
        type node = N.node
        type tree = node Tree.tree

        (* generic function that gets a condition and a merge function and
        * return the synthtized result *)
        let synth_func cond merge = function 
            |Empty -> failwith "synth_exists: empty llist"
            |ll ->
                    let rec check l' =
                        cond (fun a -> synth_rec_int a (Llist.tl l')) (Llist.hd l')
                    and synth_rec_int acc = function
                        |Empty -> acc
                        |l -> merge acc (check l)
                    in check ll
        ;;
            
        (* check when I should stop or go on in the visit *)
        let synth_cond_exists synth_rec = function
            |Leaf(n) when (n#status = Closed) -> Leaf(n)
            |Leaf(_) as a -> synth_rec a
            |_ -> failwith "synth_exists: Tree"

        (* pass information from the last visited branch to the new one *)
        let synth_merge_exists acc next = next ;;

        (* existential branching *)
        let synth_func_exists = synth_func synth_cond_exists synth_merge_exists;;

        (* check when I should stop or go on in the visit *)
        let synth_cond_forall synth_rec = function
            |Leaf(n) when (n#status = Open) -> Leaf(n)
            |Leaf(_) as a -> synth_rec a
            |_ -> failwith "synth_exists: Tree"

        (* pass information from the last visited branch to the new one *)
        let synth_merge_forall acc next = next ;;

        (* universal branching *)
        let synth_func_forall = synth_func synth_cond_forall synth_merge_forall;;


        class virtual rule =
            object
                method virtual check : node -> context
                method virtual down  : context -> tree
                method virtual up    : tree Llist.llist -> tree
            end

        class virtual exist_rule =
            object
                inherit rule
                method up = synth_func_exists
            end

        class virtual forall_rule =
            object
                inherit rule
                method up = synth_func_forall
            end

        class virtual linear_rule =
            object
                inherit rule
                method up tl = Llist.hd tl
            end
    end 
