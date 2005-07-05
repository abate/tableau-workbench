
module type S =
    sig
        type 'a sbl = ('a list) Data.Substlist.t
        type 'a pattern = { pid : int ; pmatch : 'a sbl -> 'a list -> 'a sbl }
        type 'a action  = { aid : int ; paction : 'a sbl -> 'a list }
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
        type 'a sbl = ('a list) Data.Substlist.t
        type 'a pattern = { pid : int ; pmatch : 'a sbl -> 'a list -> 'a sbl }
        type 'a action  = { aid : int ; paction : 'a sbl -> 'a list }
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
