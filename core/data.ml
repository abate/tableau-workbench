
(*
module Substlist = Map.Make(
    struct
        type t = string
        let compare = Pervasives.compare
    end)
;;
*)

module type S =
    sig
    type t
    type bt
    end

