
(* define all basic data types *)

module Type =
    struct
        type t = Comptypes.mixlist
        type sbl = t Data.Substlist.t
    end

module Fmap = Fmap.Make(struct type t = Basictype.mixtype end)

module Match =
    struct
        type t = Comptypes.mixlist
        let get_list s i = match s with
            |#Comptypes.mixlist as s' -> failwith "ddd"
            |`FMap(s) -> s#get i
    end

module Store =
    struct
        type store = [
            | Comptypes.mixlist 
            |`FMap of Fmap.fmap
            ]
        let copy = function
            |#Comptypes.mixlist as t -> Comptypes.copy t
            |`FMap(s) -> `FMap(s#copy)
    end
    
module Node = Node.Make(Store)

module NodePattern = NodePattern.Make(Type)

module Partition = Partition.Make(NodePattern)

module Tree = Tree.Make(Node)
module Rule = Rule.Make(Node)(Tree)
module Strategy = Strategy.Make(Rule)
module Visit = Visit.Make(Tree)(Strategy)
(* module Partition = Partition.Make(Type)(Node) *)
