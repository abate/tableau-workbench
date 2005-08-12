
let modules = Hashtbl.create 17;;
let are_loading = Hashtbl.create 17;;
let twb_modules = ["twbcore";"twbtypes";"twbseq";"twbintf"];;

let find_in_path path name ext =
    let filename = ((String.uncapitalize name) ^ ext) in
    print_string filename;
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

let rec load_module modname path ext =
    try
        Hashtbl.find modules modname
    with
        Not_found ->
            try
                Hashtbl.add modules modname ();
                Hashtbl.add are_loading modname ();
                Printf.printf "Loading: %s\n" modname;
                Dynlink.loadfile (modname);
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
                            load_module (find_in_path path depend ext) path ext;
                            Hashtbl.remove modules modname;
                            load_module modname path ext
                        with Not_found ->
                            failwith ("Cannot find "
                            ^String.lowercase(depend)^ext^" in "^
                            (List.fold_left (fun s x -> s^x) " " path))
                    end
;;

let load_camlp4 () =
    let version = Sys.ocaml_version in
    try
        let stdlib = "/usr/lib/ocaml/"^version^"/stdlib.cma" in
        let gramlib = "/usr/lib/ocaml/"^version^"/camlp4/gramlib.cma" in
        Printf.printf "Loading: %s ..." stdlib;
(*        Dynlink.loadfile (stdlib); *)
        print_endline "done.";
        Printf.printf "Loading: %s ..." gramlib;
        Dynlink.loadfile (gramlib);
        print_endline "done.";
    with
    | Dynlink.Error(Dynlink.Unavailable_unit(depend))
    | Dynlink.Error(
        Dynlink.Linking_error(_,Dynlink.Undefined_global(depend))
        ) -> failwith ("Cannot find "^String.lowercase(depend))
;;

let load_library twblib =
    try
        List.iter (fun m ->
            load_module
            (find_in_path [twblib] m ".cma") 
            [twblib] ".cma"
        ) twb_modules
    with Not_found -> failwith ("Load Twb Library in "^twblib^" failed")
;;

let load_logic logiclib logicname =
    load_module
    (find_in_path [logiclib] logicname ".cmo")
    [logiclib] ".cmo"
;;

let load twblib logiclib logicname =
        Dynlink.init();
        load_camlp4 ();
        load_library twblib;
        load_logic logiclib logicname
;;

