
let trace = ref false
let level = ref 0
let rulecounter = ref 0

let print_down name sbl node parentid =
    let _ = incr rulecounter in
    if !trace then
        begin
            if !level > 0 then
                Printf.printf "Substitution List: \n%s\n----\n" sbl#to_string
            else ()
            ;
            let (m,h,_) = node#get in
            let s = if !level > 0 then "Apply: " else "" in
            Printf.printf
            "%s%s ( %d -> %d )\n%s\n%s\n"
            s name parentid !rulecounter m#to_string (h#to_string true)
        end
    else ()

let print_up name node =
    if !trace && !level > 0 then
        begin
            let (_,_,v) = node#get in
            Printf.printf
            "Up %s \n%s\n----\n"
            name (v#to_string true)
        end
    else ()

let print_check name node =
    if !trace && !level > 1 then
        begin
            let (m,h,_) = node#get in
            Printf.printf
            "Check %s \n%s\n%s\n-----\n"
            name m#to_string (h#to_string true)
        end
    else ()
