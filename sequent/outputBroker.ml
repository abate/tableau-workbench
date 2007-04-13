
let trace = ref false
let level = ref 0
let rulecounter = ref 0

let print_down name node parentid =
    let _ = incr rulecounter in
    if !trace then
        begin
            let (m,h,_) = node#get in
            Printf.printf
            "%s ( %d -> %d )\n%s\n%s\n\n"
            name parentid !rulecounter m#to_string (h#to_string true)
        end
    else ()

let print_up name node =
    if !trace && !level > 0 then
        begin
            let (_,_,v) = node#get in
            Printf.printf
            "Up %s \n%s\n"
            name (v#to_string true)
        end
    else ()

let print_check name node =
    if !trace && !level > 1 then
        begin
            let (m,h,_) = node#get in
            Printf.printf
            "Check %s \n%s\n%s\n\n"
            name m#to_string (h#to_string true)
        end
    else ()
