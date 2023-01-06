(* Exercise 1 *)
  (* Do not forget part a) ! *)
  (* 1.b) *) 
  (* Hint: some of these may not be possible. Just comment them out *)

(* Impossible: We can't just magically summon a type.
   This could be possible with (List.hd []), but this will throw an exception :) *)
(* let ex1b1 : 'a -> 'b -> 'c = ... *)
(* The I combinator *)
let ex1b2 : 'a -> 'a = fun a -> a
(* True/False encodings in Lambda calculus *)
let ex1b3 : 'a -> 'b -> 'a = fun a b -> a
let ex1b4 : 'a -> 'b -> 'b = fun a b -> b
(* Impossible: Same reason as before. *)
(* let ex1b5 : 'a -> 'b = ... *)
(* Application *)
let ex1b6 : ('a -> 'b) -> 'a -> 'b = fun f a -> f a
(* Some kind of function composition. *)
let ex1b7 : ('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c = fun f g a -> f a (g a)

  (* 1.c) *) 
let ex1c: ('a -> 'b -> 'c) -> ('d -> 'a) -> ('d -> 'b) -> 'd -> 'c = fun f g h x -> f (g x) (h x)
(* A 3-fork from APL, (f g h) x = f (g x) (h x), e.g. (+/÷≢)Iv obviously computes the mean of a vector. *)


(* Exercise 2 *)
type ('a, 'b) or' = L of 'a | R of 'b
type ('a, 'b) and' = 'a * 'b
type ('a, 'b) equiv = ('a -> 'b) * ('b -> 'a)
  (* 2.a) *) 
let ex2a : ('a -> 'b, 'a -> 'a) or' = R (fun a -> a)
  (* 2.b) *)
(* Generally, to prove equivalence we have to prove that we can turn one of the statements into another somehow.
   Example here, we prove the commutativity of logical conjunction: *)
let ex2b :  ((('a, 'b) and', 'c) and', ('a, ('b, 'c) and') and') equiv =
  let shrongle : (('a, 'b) and', 'c) and' -> ('a, ('b, 'c) and') and' = fun ((x, y), z) -> (x, (y, z)) in
  let dongle : ('a, ('b, 'c) and') and' -> (('a, 'b) and', 'c) and' = fun (x, (y, z)) -> ((x, y), z) in
  (shrongle, dongle)
  (* 2.c) *)
(* Same here: We curry and uncurry a function, e.g. arbitrarily convert between ('a * 'b) -> c and a -> b -> c. Trivial. *)
let ex2c: (('a, 'b) and' -> 'c, 'a -> 'b -> 'c) equiv =
  let forward = fun f (a, b) -> f a b in
  let backward = fun f a b -> f (a, b) in
  (backward, forward)
  (* 2.d) *)
(* A bit more involved example of the same logic. *)
let ex2d: (('a, ('b, 'c) and') or', (('a, 'b) or', ('a, 'c) or') and') equiv =
  let foward : ('a, ('b, 'c) and') or' -> (('a, 'b) or', ('a, 'c) or') and' = fun x -> match x with
    | L a -> (L a, L a)
    | R (b, c) -> (R b, R c) in
  let backward : (('a, 'b) or', ('a, 'c) or') and' -> ('a, ('b, 'c) and') or' = fun (x, y) -> match (x, y) with
    | (L a, L b) -> L a
    | (R b, R c) -> R (b, c)
    | (L a, R c) -> L a
    | (R b, L a) -> L a
  in (foward, backward)

(* Exercise 3 *)
  (* 3.a) *)
(* Unit type. *)
type true' = unit
let is_true: true' = ()

  (* 3.b) *)
(* In Haskell we could define this as newtype Void = Void Void. In OCaml - no idea. *)
type false' = | (* Replace this with your own definition, if possible *)

  (* 3.c) *) 
let exfalso (k:false') = (match k with _ -> .) (* Replace this with something corresponding to your own definition of false', if possible *)

  (* 3.d) *)
type 'a neg = 'a -> false'
(* The OCaml typechecker is dumb like a bag of hammers so we have to annotate types ourselves. *)
let ex3d1 : (('a neg, 'b neg) and', (('a, 'b) or') neg) equiv =
  let forward : ('a neg, 'b neg) and' -> (('a, 'b) or') neg = fun (a, b) x -> match x with
    | L a' -> a a'
    | R b' -> b b' in
  let backward (f : (('a, 'b) or') neg) : ('a neg, 'b neg) and' = (
    let left = fun a -> f (L a) in
    let right = fun b -> f (R b) in (left, right)) in
  (forward, backward)
    
let ex3d2 : ('a neg, 'b neg) or' -> (('a, 'b) and') neg =
  fun x -> match x with
    | L a -> fun (a', b) -> a a'
    | R b -> fun (a, b') -> b b'

(* Exercise 4 *)
  (* Do not forget part a) ! *)

(* This can not be solved because we don't know what type is 'a. We can't just magically summon a type.
   You disallowed using stuff like List.hd [] or using divergence to summon them in.
   We can experiment with many things:

   let ex4b1 : ('a, 'a neg) or' = R (fun a -> a) ;;
   val ex4b1 : (false', false' neg) or' = R <fun>

   let ex4b1 : ('a, 'a neg) or' =
    L (fun a -> a) ;;
   val ex4b1 : ('a -> 'a, ('a -> 'a) neg) or' = L <fun>

   Both of these examples are important, because they show that we just can't summon a type out of nowhere.
   We can use an identity function, we can implement a single monomorphisation of our type, but nothing more.
   Also our type system is slightly too weak to make some bounds on literal values which this would require.
 *)

  (* 4.b) *)
(* Now this is way easier, because we are /given/ a type now. *)
(* Viva la ex falso *)
let ex4b1 : ('a, 'a neg) or' -> 'a neg neg -> 'a =
  fun x y -> match x with
    | L a -> a
    | R b -> exfalso (y b)

(* Proving "A or not A" is impossible without using the non-termination
   or exception tricks. So I'm afraid that you're not going to bestow
   any of us with the undying fame ;) *)

(* Exercise 5 *)
  (* 5.a) *)

(* Before we jump into this problem, some background. What we're implementing right now is not
   classical logic, rather, it's intuitionist logic. As such:
    - the law of excluded middle does not apply (('a, 'a neg) or').
    - ('a neg neg) is not equivalent to 'a.
    - 'a -> 'a neg neg holds.
    - 'a neg neg -> 'a does not. *)

let ex5b1 : ('a, 'a neg) or' neg neg =
  fun k -> k (R (fun a -> k (L a))))

  (* 5.b) *)
  
let ex5b2 : ('a neg neg -> 'a) neg neg =
  fun k -> k (fun a -> exfalso (a (fun b -> k (fun c -> b))))
         
  (* 5.c *)
let ex5b3 : (('a neg -> 'b neg) -> 'b -> 'a) neg neg =
  fun k -> k (fun (a : 'a neg -> 'b neg) (b : 'b) : 'a
    -> (a (fun c -> c) b))

  (* 5.d *)
let ex5b4 : ((('a -> 'b) -> 'a) -> 'a) neg neg =
  fun k -> k (fun (a : ('a -> 'b) -> 'a) : 'a -> (a (fun b -> k (fun c -> c))))
