
module Make(T : TwbSet.ValType)(H : TwbHash.ValType) = struct

    module DataType = DataType.Make(T)(H)
    open DataType

    let __strategy : (Strategy.node -> Strategy.m) option ref = ref None
    let __matchpatt : (T.t -> string) option ref = ref None
    let __inputparser : (string -> T.t list) option ref = ref None
    let __printer : (T.t -> string) option ref = ref None
    let __substitute : (T.t -> T.t -> T.t -> T.t) option ref = ref None
    let __simplification : (T.t -> T.t -> T.t ) option ref = ref None
    let __history_list : (string * H.t * history_type) list option ref = ref None
    let __pp : (T.t list -> T.t list) option ref = ref None
    let __neg : (T.t list -> T.t list) option ref = ref None
    let __exit : (Variable.store list -> string) option ref = ref None
    let __options : (Arg.key * Arg.spec * Arg.doc) list option ref = ref None
    let __use_cache : bool ref = ref false

end
