
module type S =
    sig
        type t 
        type bt 
        type hist
        type sbl = (t,bt) Sbl.st
        type map = (bt, bt Sets.st) Gmap.mt
        type pattern = { pid : string ; pmatch : sbl -> bt list -> sbl }
        type action  = { aid : string ; paction : sbl -> hist -> hist list -> bt list }
    end

module Make (T : sig type t type bt type hist end) =
    struct
        type t = T.t
        type bt = T.bt
        type hist = T.hist
        type sbl = (t,bt) Sbl.st
        type map = (bt, bt Sets.st) Gmap.mt
        type pattern = { pid : string ; pmatch : sbl -> bt list -> sbl }
        type action  = { aid : string ; paction : sbl -> hist -> hist list -> bt list }
        let newpatt id pmatch = { pid = id ; pmatch = pmatch }
        let newact id paction = { aid = id ; paction = paction }
    end
