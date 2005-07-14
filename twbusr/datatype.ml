
(* define all basic data types *)

module Type =
    struct
        type t = Comptypes.mixlist
    end

module Fmap = Gmap.Make(
    struct
        type t = Basictype.mixtype
        type c = Comptypes.Mtlist.listobj
        let make () = new Comptypes.Mtlist.listobj
    end)

module Hmap = Hmap.Make(
    struct
        type t = Type.t
        let copy = Comptypes.copy
    end
)

module Store =
    struct
        type store = Fmap.map
        let copy s = s#copy
        let make () = new Fmap.map
    end
    
module History =
    struct
        type store = Hmap.map
        let copy s = s#copy
        let make () = new Hmap.map 
    end

module NodeType1 = 
    struct
        type elt = { map : Store.store; hist : History.store }
        let copy e = { map = Store.copy e.map; hist = History.copy e.hist }
    end
    
module NodeType = 
    struct
        type elt = ( Store.store * History.store)
        let copy (m,h) = ( Store.copy m, History.copy h )
    end

module NodeI = Node.Make(NodeType)

module NodePatternFunc = NodePattern

module NodePattern = NodePatternFunc.Make(
    struct
        type bt = Basictype.mixtype
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

module Rule = Rule.Make(Type)(NodeI)
module Strategy = Strategy.Make(Rule)
module Visit = Visit.Make(Rule)(Strategy)

