
source K

open Twblib
open Klib

TABLEAU

RULE KD ( <> A ) ; [] X ; Z --- A ; X END
RULE Id { a } ; { ~ a } === Close END
RULE And A & B === A ; B END
RULE Or { A v B } === A | B END

END

PP := List.map nnf
NEG := List.map neg

let saturation = tactic ( (And ! Or ! Id) )
STRATEGY tactic ( ( saturation ! Kd )* )

MAIN
