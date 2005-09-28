

class type ['t] mt =
  object ('a)
    method add : string -> 't -> 'a
    method copy : 'a
    method find : string -> 't
    method to_string : string
  end

module type ValType =
    sig
        type t
        val copy : t -> t
        val to_string : t -> string
    end


module Make(T: ValType) :
    sig
        class map : [T.t] mt
    end
= struct
    
    module FMap = Map.Make (
        struct
            type t = string
            let compare = compare
        end
    )

    let copy m = FMap.fold (
        fun k v m' -> FMap.add k (T.copy v) m'
    ) m FMap.empty

    class map =
        object(self)

            val data : T.t FMap.t = FMap.empty

            method private addel fm p e =
                try
                    let s = FMap.find p data
                    in FMap.add p e (FMap.remove p data)
                with Not_found -> FMap.add p e data 

            (* insertion is O(log n) where n is the number of keys *)
            method add p e = {< data = self#addel data p e >}

            (* given a pattern return an element list *)
            (* find is O(log n) where n is the number of keys *)
            method find p = FMap.find p data
            
            (* copy is o(n*m)
             * where n is the number of keys 
             * and m is the number of element in the value *)
            method copy = {< data = (copy data) >}

            method to_string =
                FMap.fold (
                    fun k v s -> Printf.sprintf "%s\n%s:%s" s k (T.to_string v)
                ) data ""
 
        end
        
end
