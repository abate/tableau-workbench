
module Substlist = Map.Make(
    struct
        type t = string
        let compare = Pervasives.compare
    end)

type status =
    | Open
    | Closed
    | User of string (** User defined status *)


module type S = sig type t end

