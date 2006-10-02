
include UserData
    
module NodeType =
    struct
        type elt = ( Store.store * History.store * Variable.store )
        let copy (m,h,v) = ( Store.copy m, History.copy h, Variable.copy v )
        let to_string (m,h,v) =
            Printf.sprintf "%s\n%s\n%s"
            (Store.to_string m)
            (History.to_string h)
            (Variable.to_string v)
        let marshal (m,h,v) =
            string_of_int (Hashtbl.hash (m#to_string ^ h#to_string))
    end

module Node = Node.Make(NodeType)
module Cache = Cache.Make(Node)
    
module NodePatternFunc = NodePattern

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
            method virtual use_cache : bool
        end
    let skip : rule = object
        method check node =
            RuleContext.newcontext (
                Enum.empty (),
                new Substitution.substitution,
                node
                )
        method down context =
            let (_,_,node) = context#get in Tree.Tree(Llist.return node)
        method up _ tl = Llist.hd tl
        method use_cache = false
    end
    
end

module Strategy = Strategy.Make(Node)(Rule) 
module Visit = Visit.Make(Node)(Rule)(Strategy)

