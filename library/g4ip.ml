(* This is a version of G4ip *)

(* A prover for intuitionistic propositional logic where backward  *)
(* proof search terminates without histories or loop checks.       *)

CONNECTIVES [ "~";"&";"v";"->";"<->";"=>" ]
GRAMMAR
formula :=
     Atom | Falsum
    | formula & formula
    | formula v formula
    | formula -> formula
    | formula <-> formula
    | ~ formula
;;

expr := formula ;;
node := mset => singleton ;;
END

SEQUENT

  RULE Id
            Close
         ==============
          { a } => { a }
  END

  RULE Bottom 
            Close
         ==============
          { Falsum } =>
  END

  RULE AndL
                A ; B =>
           =============
            { A & B } =>
  END

  RULE AndR
            => A | => B
            ============
            => { A & B }
  END

  RULE OrL
            A => | B =>
           ============
           { A v B } =>
  END

  RULE OrR
            => A  || =>  B
           ================
              => { A v B }
  END

  RULE ImpR
               A => B
            ============
            => { A -> B }
  END

  RULE ImpMP
               a ; B  =>
           =====================
           { a } ; { a -> B } =>
  END

  RULE ImpAnd
                C -> (D -> B) =>
           =====================
             { (C & D) -> B } =>
  END


  RULE ImpOr
              C -> B ; D -> B =>
           =====================
             { (C v D) -> B } =>
  END

  RULE ImpImp
              D -> B ; C => D | B => E 
              ------------------------- 
                { (C -> D) -> B } => E
  END

END

STRATEGY :=
 let saturate = tactic (Id|Bottom|ImpMP|AndL|OrL|AndR|ImpOr|ImpAnd)
 in tactic ( ((saturate)* ;  (ImpImp|OrR))* )

let exit = function 
    |"Open" -> "Not Derivable"
    |"Closed" -> "Derivable"
    |_ -> assert(false)

EXIT := exit (status@1)

MAIN

