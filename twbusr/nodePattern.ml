
module type S =
    sig
        type t
        type sbl = (t list) Data.Substlist.t
        type 'a pattern = { pid : int ; pmatch : sbl -> 'a list -> sbl }
        type 'a action  = { aid : int ; paction : sbl -> 'a list }
        type 'a nodepattern =
            { pname : string;
              chained : 'a pattern list;
              strict : 'a pattern list;
              loose : 'a pattern list
            }
        type 'a nodeaction = { aname : string; action : 'a action list }
    end

module Make (T : Data.S) =
    struct
        type t = T.t
        type sbl = (t list) Data.Substlist.t
        type 'a pattern = { pid : int ; pmatch : sbl -> 'a list -> sbl }
        type 'a action  = { aid : int ; paction : sbl -> 'a list }
        type 'a nodepattern =
              { pname : string;
                chained : 'a pattern list;
                strict : 'a pattern list;
                loose : 'a pattern list
              }
        type 'a nodeaction = { aname : string; action : 'a action list }
        let newpatt id pmatch = { pid = id ; pmatch = pmatch }
        let newact id paction = { aid = id ; paction = paction }
    end
