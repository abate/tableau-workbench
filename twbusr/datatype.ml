
(* define all basic data types *)

module Type : Data.S =
    struct
        type type_t = Comptypes.mixlist
        type substlist = type_t Data.Substlist.t
    end

module Pattern = Pattern.Make(struct type pattern = Comptypes.mixlist_p end)
module Node = Node.Make(struct type store = Comptypes.mixlist end)

module MatchType = 
    struct
        type store = Comptypes.mixlist
        type pattern = Pattern.pattern
        type basictype = Basictype.mixtype
        let match_type = Partition.match_fmap
    end

module MatchNode = Matchnode.Make(MatchType)(Pattern)
module Tree = Tree.Make(Node)
module Rule = Rule.Make(Node)(Tree)
module Strategy = Strategy.Make(Rule)
module Visit = Visit.Make(Tree)(Strategy)
(* module Partition = Partition.Make(Type)(Node) *)
