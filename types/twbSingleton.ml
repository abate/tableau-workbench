
module Make(T: TwbSet.ValType) = struct

        type t = T.t
        module Set = TwbSet.Make(T)

        class map (_ : (T.t -> string)) =
            object(self)

                val data = new Set.set

                method addlist ( id : string ) = function
                    |[] -> {<>}
                    |[h] -> self#add h
                    |_ -> failwith "Singleton"
                method add e = {< data = (new Set.set)#add e >}
                method del (_ : T.t) = {< data = new Set.set >}
                method replace (_ : string) (_ : Set.set) = {< data = new Set.set >}
                method find (_ : string) = data
                method copy = {< data = data#copy >}
                method empty = {< data = new Set.set >}
                method to_string = ""
            end

    end

