
let modules = Hashtbl.create 17;;
let are_loading = Hashtbl.create 17;;

let find_in_path path name =
    let filename = ((String.uncapitalize name) ^ ".cmo") in
    if not (Filename.is_implicit filename) then
        if Sys.file_exists filename then filename else raise Not_found
        else
            begin
                let rec try_dir = function
                    | [] -> raise Not_found
                    | dir::rem ->
                            let fullname = Filename.concat dir filename in
                            if Sys.file_exists fullname then fullname
                            else try_dir rem
                in try_dir path
            end

let rec load_module modname path =
    try
        Hashtbl.find modules modname
    with
        Not_found ->
            try
                Hashtbl.add modules modname ();
                Hashtbl.add are_loading modname ();
                (* Printf.printf "Loading: %s ..." modname; *)
                Dynlink.loadfile (modname);
                (* print_endline "done."; *)
                Hashtbl.remove are_loading modname
            with
            | Dynlink.Error(Dynlink.Unavailable_unit(depend))
            | Dynlink.Error(
                Dynlink.Linking_error(_,Dynlink.Undefined_global(depend))
                ) ->
                    begin
                        try
                            if Hashtbl.mem are_loading depend
                            then failwith ("Crossing with "^depend);
                            load_module (find_in_path path depend) path;
                            Hashtbl.remove modules modname;
                            load_module modname path
                        with Not_found ->
                            failwith ("Cannot find "
                            ^String.lowercase(depend)^" in "^
                            (List.fold_left (fun s x -> s^x) " " path))
                    end
            | Dynlink.Error(e) -> failwith (Dynlink.error_message e)
;;

let load_camlp4 () =
    let version = Sys.ocaml_version in
    let stdlib = "/usr/lib/ocaml/"^version^"/stdlib.cma" in
    let camlp4_modules = ["odyl";"camlp4"] in
    try
        (* Printf.printf "Loading: %s ..." stdlib; *)
        Dynlink.loadfile (stdlib);
        (* print_endline "done."; *)
        List.iter (fun m ->
            let file = Printf.sprintf "/usr/lib/ocaml/%s/camlp4/%s.cma" version m in
            (* Printf.printf "Loading: %s ..." file; *)
            Dynlink.loadfile(file);
            (* print_endline "done." *)
        ) camlp4_modules
    with
    Dynlink.Error(e) -> failwith (Dynlink.error_message e)
;;

let load_library twblib =
    let twb_modules = [(* "twbcore";"twbtypes";*)"twbseq";"twbintf"] in
    try
        List.iter (fun m ->
            let file = Printf.sprintf "%s/%s.cma" twblib m in
            (* Printf.printf "Loading: %s ..." file; *)
            Dynlink.loadfile(file);
            (* print_endline "done." *)
        ) twb_modules
    with
    Dynlink.Error(e) -> failwith (Dynlink.error_message e)
;;

let load_logic logiclib logicname =
    try
        load_module (find_in_path [logiclib] logicname) [logiclib]
    with Not_found -> failwith "Loading error"
;;
let load twblib logiclib logicname =
        Dynlink.init();
        Dynlink.allow_unsafe_modules true;
        load_camlp4 ();
        Dynlink.allow_unsafe_modules false;
        Dynlink.default_available_units ();
        load_library twblib; 
        load_logic logiclib logicname 
;;

