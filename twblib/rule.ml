
open Llist
open Node
open Tree

module type S =
    sig
        type node
        type tree
        class rule_context : object val context : 'a list end
        
        class virtual rule :
            object
                method virtual check : node -> rule_context
                method virtual down : node -> tree
                method virtual up : tree Llist.llist -> tree
            end
            
        class virtual forall_rule :
            object
                method virtual check : node -> rule_context
                method virtual down : node -> tree
                method virtual up : tree Llist.llist -> tree
            end
            
        class virtual exist_rule :
            object
                method virtual check : node -> rule_context
                method virtual down : node -> tree
                method virtual up : tree Llist.llist -> tree
            end

      end

module Make (N:Node.S) (T:Tree.S with type node = N.node) =
    struct
    
    type node = T.node
    type tree = T.tree
    open T

    (* generic function that gets a condition and a merge function and
    * return the synthtized result *)
    let synth_func f m = function 
        |Empty -> failwith "synth_exists: empty llist"
        |l ->
                let rec check l = f (fun a -> synth_rec_int a l) (Llist.hd l)
                and synth_rec_int acc = function
                    |Empty -> acc
                    |l -> m acc (check l)
                in check l
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

    (* this is the rule context and contains the substitution list *)
    class rule_context =
        object
            val context = []
        end

    class virtual rule =
        object
            method virtual check : node -> rule_context
            method virtual down : node -> tree
            method virtual up : tree Llist.llist -> tree
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

end
