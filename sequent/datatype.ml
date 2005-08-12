
(* define all basic data types *)

module Type =
    struct
        type t = Comptypes.mixlist
        type bt = Basictype.mixtype
    end

module Fmap = Gmap.Make(
    struct
        type t = Type.bt
        type c = Comptypes.Mtlist.listobj
        let make () = new Comptypes.Mtlist.listobj
    end)

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

module NodeType = 
    struct
        type elt = ( Store.store * History.store)
        let copy (m,h) = ( Store.copy m, History.copy h )
        let to_string (m,h) =
            Printf.sprintf "%s%s"
            (Store.to_string m)
            (History.to_string h)
    end

module Node = Node.Make(NodeType)

module NodePatternFunc = NodePattern

module NodePattern = NodePatternFunc.Make(
    struct
        type bt = Type.bt
        type t = Type.t
        type key = int
    end
)

module HistPattern =  NodePatternFunc.Make(
     struct
        type bt = Type.t
        type t = Type.t
        type key = string
    end
)

module Partition = Partition.Make(NodePattern)(HistPattern)
module Build = Build.Make(NodePattern)

module RuleContext =
    struct
    type t = (HistPattern.sbl *
                (NodePattern.bt, NodePattern.bt Sets.st) Gmap.mt) Enum.t * 
                    HistPattern.sbl * Node.node

    class context ((e,s,n) : t) = 
        object
            val data = (e,s,n)
            method set e = {< data = e >}
            method get = data
            method is_valid = not(Data.Substlist.is_empty s)
        end
    end

module Rule = UserRule.Make(Type)(Node)(struct type t = RuleContext.t end)
module Strategy = Strategy.Make(Rule)
module Visit = Visit.Make(Rule)(Strategy)

