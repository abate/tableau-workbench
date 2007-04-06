
module Make (T : TwbSet.ValType) : sig class set : [T.t] TwbSet.ct end =
    struct
        module L = TwbList.Make(T)
        class set = L.olist
    end
