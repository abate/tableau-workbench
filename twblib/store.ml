
(* this class is used to build user defined datatypes. it's
* an open type and it is used to instanciate a concrete
* instance of the Store Module *)
class virtual ['mt] store_open =
    object(self: 'store)
        method virtual add : 'mt -> 'store
        method virtual del : 'mt -> 'store
        method virtual copy : 'store
        method virtual string_of : ('mt -> string) -> string
    end

(* this type is used by the functors in the twblib *)
module type S =
    sig
        type elt
        class virtual store :
            object
                inherit [elt] store_open
            end
    end
