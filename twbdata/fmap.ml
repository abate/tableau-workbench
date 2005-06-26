
(* this is the data structure to store formulae/basictypes
 * and it's optimized to retrive formulae according to a
 *  pattern *)

open Basictype
open Store

module FMap = Map.Make (
    struct
        type t = int
        let compare = compare
    end
)

type nodet = int * mixtype list 

class fmap matchpatt =
    object(self)
        inherit [nodet] store_open

        val mutable data = FMap.empty

        method data = data
        method assign s = {< data = s#data >}

        method private pattern = matchpatt
        
        method add (p,l) =
            match p with
            |0 ->
                    let newdata = List.fold_left (
                        fun fm e ->
                            let (p,l) = self#pattern e in
                            let oldlist = try FMap.find p fm
                                with Not_found ->
                                    failwith "fmap: this term doesn't match any pattern"
                            in FMap.add p (l@oldlist) (FMap.remove p data)
                    ) data l
                    in {< data = newdata >}
            |_ ->
                    let oldlist = try FMap.find p data 
                        with Not_found ->
                            failwith "fmap: this term doesn't match any pattern"
                    in {< data = FMap.add p (l@oldlist) (FMap.remove p data) >}

        (* given a pattern return a sbl *)
        method get p = 
            try FMap.find p data
            with Not_found ->
                failwith "fmap: this term doesn't match any pattern"
            
        (* XXX: *)
        method del e = {< >}
        
        method export = El([])
        method copy = {< data = data >}
    end
;;

