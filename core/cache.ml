
module type S =
sig
    type node
    class cache :
          object('cache)
              method add  : node -> node -> unit
              method mem  : node -> bool
              method find : node -> node option
              method to_string : string
              method stats : string
          end
end


module Make (N:Node.S) =
  struct

        type node = N.node
        module Hash = Hashtbl.Make(
            struct 
                type t = node
                let equal n1 n2 = print_string "equal" ; n1#is_equal n2
                let hash n = Hashtbl.hash n#get
            end)
        
        class cache =
            object(self)
                val data : node Hash.t = Hash.create 51
                val mutable hits = 0
                val mutable miss = 0
                
                method mem k = 
                    if Hash.mem data k then
                        ( print_string "Hit";
                             hits <- hits +1; true)
                    else (
                        print_string "Mem:";
                        print_endline k#to_string;
                        print_endline self#to_string;
                        print_endline "Miss--";
                        miss <- miss +1; false)
                
                method find k =
                    try Some(Hash.find data k)
                    with Not_found -> None
                    
                method add k v = 
                    print_string "Add: ";
                    print_int (Hashtbl.hash k);
                    print_string k#to_string;
                    print_endline "-----";
                    Hash.replace data k v
                    
                method to_string =
                    Hash.fold (
                        fun k v s ->
                            Printf.sprintf "%s\nkey:%s\nvalue:%s"
                            s k#to_string v#to_string
                    ) data ""

                method stats = 
                    Printf.sprintf
                    "Cache results:\nHits:%d\nMiss:%d\nElements in the cache:%d\n"
                    hits miss (Hash.length data)
            end
    end

