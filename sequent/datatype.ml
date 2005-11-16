
(* define all basic data types *)

module Type =
    struct
        type t = Comptypes.mixlist
        type bt = Basictype.mixtype
    end

module Fmap = Gmap.Make(
    struct
        type t = Type.bt
        type c = Comptypes.Set.set
        let make () = new Comptypes.Set.set
    end)

(*
with Comptypes.Mtlist.listobj are multisets
module Fmap = Gmap.Make(
    struct
        type t = Type.bt
        type c = Comptypes.Mtlist.listobj
        let make () = new Comptypes.Mtlist.listobj
    end)
*)

module Hmap = Hmap.Make(
    struct
        type t = Type.t
        let copy = Comptypes.copy
        let to_string = Comptypes.string_of_mixlist
    end
)

module Store =
    struct
        type store = Fmap.map
        let copy s = s#copy
        let to_string s = s#to_string
        let make () = new Fmap.map
    end
    
module History =
    struct
        type store = Hmap.map
        let copy s = s#copy
        let to_string s = s#to_string
        let make () = new Hmap.map 
    end

module Variable =
    struct
        type store = Hmap.map
        let copy s = s#copy
        let to_string s = s#to_string
        let make () = new Hmap.map 
    end

type history_type = History | Variable 
    
module NodeType =
    struct
        type elt = ( Store.store * History.store * Variable.store )
        let copy (m,h,v) = ( Store.copy m, History.copy h, Variable.copy v )
        let equal (m1,h1,_) (m2,h2,_) = (m1 = m2) && (h1 = h2)
        let to_string (m,h,v) =
            Printf.sprintf "%s\n%s\n%s"
            (Store.to_string m)
            (History.to_string h)
            (Variable.to_string v)
    end

module Node = Node.Make(NodeType)
module Cache = Cache.Make(Node)
    
module NodePatternFunc = NodePattern
module Substitution = Sbl.Make

module NodePattern = NodePatternFunc.Make(
    struct
        type t = Type.t
        type bt = Type.bt
        type hist = History.store
        type sbl = Substitution.substitution
    end
)

module Partition = Partition.Make(NodePattern)
module Build = Build.Make(NodePattern)

module RuleContext = RuleContext.Make(Node)(NodePattern)
module Rule =
    struct
    type t = RuleContext.t
    type node = Node.node
    type tree = node Tree.tree
    type context_type = RuleContext.ct
    type context = RuleContext.context
    class virtual rule =
        object
            method virtual check : node -> context
            method virtual down  : context -> tree
            method virtual up    : context -> tree Llist.llist -> tree
        end
    end

module Strategy = UserStrategy.Make(Rule) 
module Visit = Visit.Make(Node)(Cache)(Rule)(Strategy)

