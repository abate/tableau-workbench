
open ExtLib

module type MatchType =
    sig
        type store
        type pattern
        type basictype
        val match_type :
            store -> (pattern list * pattern list * pattern list) -> 
                (basictype Data.Substlist.t) Enum.t
    end

module Make (T:MatchType)(P:Pattern.S with type pattern = T.pattern) = 
    struct
        open P
        let match_type = T.match_type
        
        let match_node node  = function
            { name = name; chained = pl ; strict = sl; loose = ll } ->
                match_type (node#get name) (pl,sl,ll)
    end

