type 'a llist = LList of 'a * 'a llist Lazy.t | Empty
val empty : 'a llist
val push : 'a -> 'a llist -> 'a llist
val hd : 'a llist -> 'a
val tl : 'a llist -> 'a llist
val map : ('a -> 'b) -> 'a llist -> 'b llist
val of_list : 'a list -> 'a llist
val to_list : 'a llist -> 'a list
