
module type S =
    sig
    type t
    type node
    type map 
    type sbl 
    type enum = ( sbl * map ) Enum.t
    type ct = enum * sbl * node
    type context = ct Rule.ct
    val newcontext : ct -> context
    end

module Make (N: Node.S) (P: NodePattern.S) =
    struct
    type t = P.t
    type node = N.node
    type sbl = P.sbl
    type map = P.map
    type enum = ( sbl * map ) Enum.t
    type ct = enum * sbl * node

    class context ((e,s,n) : ct) =
        object
            val data = (e,s,n)
            method set e = {< data = e >}
            method get = data
            method is_valid = not(s#is_empty)
        end

    let newcontext t = new context t
    end

