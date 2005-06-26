
(* this type definition is used inside the library
 * but we don't constrain the functor. The functor
 * type and this type should be maintained consistent *)
module type S = 
    sig
        type pattern
        type nodepattern =
              { name : string;
                chained : pattern list;
                strict : pattern list;
                loose : pattern list
              }
        type nodeaction
    end

module Make (T : sig type pattern end ) =
    struct
        type pattern = T.pattern
        type nodepattern =
              { name : string;
                chained : pattern list;
                strict : pattern list;
                loose : pattern list
              }
        type nodeaction = pattern list
    end

      (*    condition: ; 
       *    action: ; *)
