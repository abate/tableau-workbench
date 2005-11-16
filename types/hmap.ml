

class type ['t] mt =
  object ('a)
    method add : string -> 't -> 'a
    method copy : 'a
    method find : string -> 't
    method mem : string -> bool
    method empty : 'a
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
    
    let copy h =
        Hashtbl.fold (fun k v tbl ->
            Hashtbl.add tbl k (T.copy v) ; tbl
        ) h (Hashtbl.create (Hashtbl.length h))
     
    class map =
        object(self)

            val data = Hashtbl.create 7
            
            method add p e =
                let h = copy data in
                let _ = Hashtbl.replace h p e in
                {< data = h >}
                
            method find p = Hashtbl.find data p
            method mem p = Hashtbl.mem data p
            method copy = {< data = copy data >}
            method empty = {< data = Hashtbl.create 7 >}
            method to_string =
                Hashtbl.fold (
                    fun k v s -> Printf.sprintf "%s\n%s:%s" s k (T.to_string v)
                    (*
                    fun k v s ->
                        if (T.to_string v) = "" then ""
                        else if s = "" then Printf.sprintf "%s:%s" k (T.to_string v) 
                            else Printf.sprintf "%s\n%s:%s" s k (T.to_string v)
                            *)
                ) data ""
 
        end
        
end
