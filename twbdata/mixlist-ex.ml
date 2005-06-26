type mixlist = [
    |`I of mixtype listobj
    |`S of set
];; 

let a1 = new set;;

let a2 = new listobj_subtype;;

let l = [`S a1;`I a2];;

type mixlist1 = [
    |`SS of setofset
    |mixlist
];;

let a3 = new setofset;;
let a5 = new setoftupleset;;

let l1 = (`SS a3)::l;;

a1#add (`Int 1);;
a1#add (`Tuple (1,2));;
a3#add (`Set a1);;
let a4 = a1#copy;;
a5#add (`TupleofSet (a1,a4));;

let a = a3#export;;

