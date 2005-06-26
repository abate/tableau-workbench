
type 'el ext_rep_open =
    | El of 'el list
    | Cont of 'el ext_rep_open list

(* this class is used to build user defined datatypes. it's
* an open type and it is used to instanciate a concrete
* instance of the Store Module *)
class virtual ['mt] store_open =
    object(self: 'store)
        method virtual assign : 'store -> 'store
        method virtual add : 'mt -> 'store
        method virtual del : 'mt -> 'store
        method virtual export : 'mt ext_rep_open
        method virtual copy : 'store
    end

(* this type is used by the functors in the twblib *)
module type S =
    sig
        type elt
        type ext_rep 
        class virtual store :
            object
                inherit [elt] store_open
            end
    end
