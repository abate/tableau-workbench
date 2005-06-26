
open ExtLib
module Substlist = Data.Substlist

exception FailedMatch

let match_type = Basictype.match_type
let match_type_fmap = Comptypes.match_type_fmap

(* Return an enumeration composed by a tuple: an enumeration of
* the input list and the list of all remaining elements *)
(* l is the pattern list
 * get is the function that return a list of formulae given a pattern
 * init() returns a fresh htbl
 * check h (p,el) returns a bool if the side conditions on the 
 * principal formula are satisfied.
 *
 * we use this function to match all the principal formuale
*)
let check (sbl,htbl) p f =
    if not(Hashtbl.mem htbl f) then
        let s = match_type sbl f p in
        let _ = Hashtbl.add htbl f () in
        Some(s,htbl)
    else None
    
let init () = (Substlist.empty, Hashtbl.create 7)

let enum store patternlist =
    let rec enum_aux = function
        |[] -> Enum.empty ()
        |patt::[] ->
                let el = Comptypes.match_type_fmap store patt in
                Enum.filter_map (fun x ->
                    check (init ()) patt x
                ) (List.enum el)
        |patt::pl ->
                let el = Comptypes.match_type_fmap store patt in
                Enum.concat (
                    Enum.map (fun x ->
                        Enum.filter_map (
                            fun tbl ->
                                check tbl patt x
                        ) (Enum.clone (enum_aux pl))
                    ) (List.enum el)
                )
    in enum_aux patternlist

(* we get all formulae associated with a pattern minus the
 * formulae that have been selected to be proncipal formulae.
 *  
 * FIXME: This could faster. I know that a formula might be 
 * in the htbl only is the patt is simular to the pattern of 
 * the principal formulea
 *)
let getset store subsl htbl patt =
    let fl =
        List.filter (
            fun f -> not(Hashtbl.mem htbl f)
        ) (Comptypes.match_type_fmap store patt)
    in
    List.fold_left (
        fun sl f -> match_type sl f patt
    ) subsl fl

let match_fmap store (pl,sl,ll) =
    try
        Enum.map (
            fun (subsl,htbl) ->
                        let tmpsl =
                            List.fold_left (
                                fun subl patt ->
                                    getset store subl htbl patt
                            ) subsl sl
                        in
                        List.fold_left (
                            fun subl patt ->
                                    getset store subl htbl patt
                        ) tmpsl ll
        ) (enum store pl)
    with FailedMatch -> Enum.empty ()

