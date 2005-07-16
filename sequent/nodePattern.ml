
module type S =
    sig
        type t 
        type bt 
        type sbl = t Data.Substlist.t
        type pattern = { pid : string ; pmatch : sbl -> bt list -> sbl }
        type action  = { aid : string ; paction : sbl -> bt list }
    end

module Make (T : sig type t type bt end) =
    struct
        type t = T.t
        type bt = T.bt
        type sbl = t Data.Substlist.t
        type pattern = { pid : string ; pmatch : sbl -> bt list -> sbl }
        type action  = { aid : string ; paction : sbl -> bt list }
        let newpatt id pmatch = { pid = id ; pmatch = pmatch }
        let newact id paction = { aid = id ; paction = paction }
    end
