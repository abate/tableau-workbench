
(* define all basic data types *)

module Type =
    struct
        type t = Comptypes.mixlist
    end

module Fmap = Fmap.Make(
    struct
        type t = Basictype.mixtype
        type c = Comptypes.Set.set
        let make () = new Comptypes.Set.set
    end)

module Store =
    struct
        type store = [
            |`FMap of Fmap.fmap
            |Comptypes.mixlist 
            ]
        let copy = function
            |`FMap(s) -> `FMap(s#copy)
            |#Comptypes.mixlist as t -> Comptypes.copy t
    end
    
module Node = Node.Make(Store)

module NodePattern = NodePattern.Make(Type)

module Partition = Partition.Make(NodePattern)
module Build = Build.Make(NodePattern)

module Tree = Tree.Make(Node)
module Rule = Rule.Make(Node)(Tree)
module Strategy = Strategy.Make(Rule)
module Visit = Visit.Make(Tree)(Strategy)
