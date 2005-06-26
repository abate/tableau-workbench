
module Substlist = Map.Make(
    struct
        type t = string
        let compare = Pervasives.compare
    end)


module type S =
    sig
        type type_t
        type substlist = type_t Substlist.t 
    end

