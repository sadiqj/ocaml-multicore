type 'a t

external make : 'a -> 'a t = "%makemutable"
external get : 'a t -> 'a = "%atomic_load"
external compare_and_set : 'a t -> 'a -> 'a -> bool = "%atomic_cas"
external fetch_and_add : int t -> int -> int = "%atomic_fetch_add"

val set : 'a t -> 'a -> unit
val exchange : 'a t -> 'a -> 'a
val incr : int t -> unit
val decr : int t -> unit
