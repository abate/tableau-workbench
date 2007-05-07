
(* This is a version of G4ip for Bi-Intuitionistic Logic BiInt     *)

(* A prover for bi-intuitionistic propositional logic where        *)
(* backward proof search terminates using histories and variables  *) 


CONNECTIVES [ "~";"&";"v";"->";"-<";"<->";">-<";"===>";"!"]
GRAMMAR
formula :=
     Atom | Verum | Falsum
    | formula & formula
    | formula v formula
    | formula -> formula
    | formula <-> formula
    | formula -< formula     (* A -< is A excludes B *)
    | formula >-< formula
    | ~ formula              (* ~ A is intuitionistic negation *)
    | ! formula              (* ! A is dual intuitionistic negation *)
;;

expr := formula ;;
node := set ===> set ;;
END

module FormulaSet = TwbSet.Make(
    struct
        type t = formula
        let to_string = formula_printer
        let copy s = s
    end
)

module FormulaSetSet = TwbSet.Make(
    struct
        type t = FormulaSet.set
        let to_string s = s#to_string
        let copy s = s#copy
    end
)

VARIABLES
  s : FormulaSetSet.set := new FormulaSetSet.set ;
  p : FormulaSetSet.set := new FormulaSetSet.set
END

let rec conjoin gamma =
    match gamma with
      []   -> formula ( Verum )
    | h::t -> formula ( h & {conjoin gamma} )

let rec disjoin delta =
    match delta with
      []   -> formula (Verum)
    | h::t -> formula ( h v {disjoin delta} )

let bigand ll =
    [conjoin (List.map (fun s -> disjoin s#elements) ll)]

let bigor ss =
    let ll = ss#elements in
    disjoin (List.map (fun s -> conjoin s#elements) ll)

let setset d =
    let ss = new FormulaSetSet.set in
    let s = (new FormulaSet.set)#addlist d in
    ss#add s

let emptysetset () = new FormulaSetSet.set 

let notin(a,b) = not(List.mem (List.hd a) b)

let conjnotin(a,b,d,g) = 
    not(List.mem (List.hd a) d) &&
    not(List.mem (List.hd b) g)

let disjnotin(a,b,d,g) =
    not(List.mem (List.hd a) d) ||
    not(List.mem (List.hd b) g)

let rec allsubsnotsub (ps,ab,d) =
    match ps with
      []   -> failwith "Error: allsubsnotsub called with empty PS"
    | [h]  -> not(List.mem h (ab@d))
    | h::t -> if List.mem h (ab@d) then false else (allsubsnotsub (t,ab,d))

let rec compute (vars,ab,d) =
    match vars with
    |p1::_ when p1#is_empty -> p1
    |[p1;p2] -> p2
    |[p1] -> setset (ab@d)
    |_ ->  assert (false)

let setofsetsunion (x,y) = x#union y

let isnotemptyandallsubsnotsub (p,ab,d) =
    not(p#is_empty) (* && allsubsnotsub (p#elements,ab,d) *)

SEQUENT

  RULE Ret
           Open
         ========= 
          G ===> D
       BACKTRACK [  s := setset(D)
                 ; p := setset(G) ]
  END

  RULE Id
               Close
         ==================
          { A } ===> { A }
       
       BACKTRACK [ s := emptysetset() 
                 ; p := emptysetset() ]
  END

  RULE False
               Close
         ==================
          { Falsum } ===>

       BACKTRACK [ s := emptysetset()
                 ; p := emptysetset() ]
  END

  RULE True
               Close
         =================
          ===> { Verum }

       BACKTRACK [s := emptysetset()
                 ;p := emptysetset() ]
  END

  RULE AndL
            G ; A & B ; A ; B ===>
           =========================
            G ; { A & B } ===> 

       COND [ disjnotin(A,B,G,G) ]
       BACKTRACK [s := s@1 ; p := p@1]
  END

  RULE AndR
            ===> A ; A & B ; D      |    ===> B ;  A & B ; D
            =================================================
                ===> { A & B } ; D

       COND [ conjnotin(A,B,D,D) ]
       BACKTRACK [ s := setofsetsunion(s@1, s@2) 
                 ; p := setofsetsunion(p@1, p@2) 
       ]
  END

  RULE OrL
            A ; A v B ; G ===> | B ; A v B ; G ===> 
           ==========================================
                   { A v B } ; G ===> 
       COND [ conjnotin(A,B,G,G) ]
       BACKTRACK [ s := setofsetsunion(s@1, s@2) 
                 ; p := setofsetsunion(p@1, p@2) 
       ]
  END

  RULE OrR
             ===> A ;  B ; A v B ; D
            =========================
             ===> { A v B } ; D
       COND [ disjnotin(A,B,D,D) ]
       BACKTRACK [ s := s@1 ; p := p@1 ]
  END

  RULE ImpL
             A -> B ; G ===>  A ; D |   B ; A -> B ; G ===>  D 
             ==================================================
                        { A -> B } ; G ===>  D 
       COND [ conjnotin(A,B,D,G) ]
       BACKTRACK [ s := setofsetsunion(s@1, s@2) 
                 ; p := setofsetsunion(p@1, p@2) 
       ]
  END


  RULE ImpR1
             ===> B ; A -> B ; D
            =====================
             ===> { A -> B } ; D 
       COND [ notin(B,D) ]
       BACKTRACK [ s := s@1 ; p := p@1 ]
  END

  RULE ImpR2
             A ; G ===> B  |||   G  ===> A -> B ; D ; bigand(p@1)
            =====================================================
                      G ===> { A -> B } ; D ; B
       COND   [ notin(A,G) ]
       BRANCH [ isnotemptyandallsubsnotsub(p@1,A -> B, D) ]
       BACKTRACK [ s := compute(s@all, G, [])
                 ; p := compute(p@all, A -> B, D) ]
  END

  RULE BigAndR
                ===> A ; D       |          ===> B ; D
            =============================================
                         ===> { A & B } ; D
       COND [ conjnotin(A,B,D,D) ]
       BACKTRACK [ s := setofsetsunion(s@1, s@2) 
                 ; p := setofsetsunion(p@1, p@2) ]
  END

END

STRATEGY := 
 let saturate = tactic (Id!False!True!AndL!OrR!ImpR1!OrL!AndR)
 in tactic ( (((saturate)* ; ImpR2 )* ; Ret)* )

MAIN
