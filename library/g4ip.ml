
(* This is a version of G4ip *)

(* A prover for intuitionistic propositional logic where backward  *)
(* proof search terminates without histories or loop checks.       *)

CONNECTIVES [ "!";"&";"v";"->";"<->";"=>";"#"]
GRAMMAR
formula :=
     Atom | Verum | Falsum
    | formula & formula
    | formula v formula
    | formula -> formula
    | formula <-> formula
    | ! formula
    | # formula
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

  RULE False
               Close
         ===================== 
          { Falsum } => 
  END

  RULE True
            Close
         ============== 
           => { Verum }
  END

  RULE NegL X -> Falsum => === ! X => END
  RULE NegR => A -> Falsum === => { ! A } END

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
           { a} ; { a -> B } => 
  END

  RULE ImpVerum
                      Verum ; B  => 
           =====================
           { Verum } ; { Verum -> B } => 
  END

  RULE ImpNeg
             ( A -> Falsum ) -> B  => 
           =====================
               { ! A -> B } => 
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
                G ; # (C -> D) -> B => E  || G => E
              ====================================
                  G ; { (C -> D) -> B } => E
  END

  RULE RajOr
               G;  D -> B ; C => D  || B ; G => E
              =====================================
                  G ; { # (C -> D) -> B } => E       
  END

END

let exit = function 
    |"Open" -> "Not Derivable"
    |"Closed" -> "Derivable"
    |_ -> assert(false)

STRATEGY := 
 let saturate = tactic (
     NegR|NegL|Id|False|True|AndL|ImpNeg|ImpVerum|
     ImpOr|ImpAnd|OrR|OrL|AndR|ImpMP|ImpR)
 in tactic ( ( (saturate)* ;  (ImpImp ; RajOr) )* )

MAIN

