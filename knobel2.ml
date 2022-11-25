
(* PROBLEM 1 *)
(* a. It looks suspiciously like a do...while loop that operates on a single variable like
   the Y combinator in lambda calculus. This lets us implement recursion just like Y combinator
   does:
     const Y = f => (x => x(x))(x => f(y => x(x)(y)))
     const F = f => (x => (x == 1 ? x : x * f(x - 1)))
     const tenbang = Y(factorial)(10)
   The type of fortytwo seems to be:
   val fortytwo : ('a -> 'a * bool) -> 'a -> 'a.
   
   It's worth noting that this isn't really the Y combinator, it's just similar. *)

let rec fortytwo (f : 'a -> ('a * bool)) (s : 'a) =
  let (n, b) = f s
  in  if b then fortytwo f n
  else n ;;

(* We rework a factorial function to just use something comparable to a while loop.
    First element in the tuple is the current n in n!, the second is the accumulator. *)
let fac x=let(a,b)=fortytwo(fun(x,y)->if x<1 then((x,y),false)else((x-1,y*x),true))(x,1)in b;;

(* It would be cool if you explained what iter, etc... are :) *)
(* I had to open the lecture notes for once, so let me just write down what these do:

let rec iter f n x =
if n < 1 then x
else iter f (n - 1) (f x)

let rec first f k =
if f k then k
else first f (k + 1)

It would also be cool if you provided OCaml code for `forall'...

I had to implement it myself:
let rec forall m n f = if m>n then true else (f m) && (forall (m+1) n f) ;; 

*)

(* The F parameter never changes so we don't include it in the tuple we iterate over. *)
let iter f n x=let(a,b)=fortytwo(fun(n,x)->if n<1 then ((0,x), false) else ((n-1,(f x)),true))(n,x)in b;;

(* First is considerably easier to implement: *)
let first f k = fortytwo(fun k->if f k then (k,false)else (k+1,true))(k);;

(* Forall also doesn't require too much fucking, but yielding values is weird.
    We will use a separate tuple slot for that. Notice how n and f are stationary.
    Notice how we separate the and clause because of short circuiting. *)

let forall m n f = let(a,b)=fortytwo(fun(m,r)->if m>n then ((0,true),false) else if (f m) then ((m+1,r),true) else ((0,false),false))(m,false)in b;;

(* PROBLEM 2 *)
(* Congratulations on making the Ackermann-Péter function look scary.
   Anyway, the problem is that this sinister device uses double recursion and we can't easily
   elide this into single tail recursion. Long story short, fortytwo can be used to implement
   tail-recursive functions. Ackermann function is doubly recursive and we can elide one
   recursive call:
int ackermann(int m, int n) {
    if (!m) return n + 1;
    return ackermann(m - 1, n ? ackermann(m, n - 1) : 1);
}
=>
int ackermannb(int m, int n) {
    for(;m;m--) {
        n = n ? ackermannb(m, n - 1) : 1;
    }
    return n+1;
}
   .. but not the other :). And we technically can't use fortytwo to implement non-tail-recursive functions like
   ackermannb.



   ALTHOUGH!
   We can pretty easily game it and gain access to recursion :)...
   Consider reading the Wikipedia article on the "Y combinator".
   Internet strangers can explain it better than me.

   We've already covered custom types and type constructors, I think,
   so I believe that this implementation of the Y combinator pleases the demon.

   Of course, i could use fourtytwo and Scott encoding to hold the call stack
   as an accumulator, but I don't think that would be allowed.

   The trick here is that the Y combinator is a paradoxical combinator:
   we can't type it normally, because a function normally wouldn't be able to take
   itself as an argument to itself. We solve this using polymorphic variants,
   or ordinary variants like I did.

   Thus I have achieved recursion without ugly hacks (references) nor breaking the
   rules (using "rec") nor using fourtytwo(!), hence I think that I deserve extra
   Dieters.
 *)

type 'a fix = Fix of ('a fix -> 'a)

let fix x = Fix x ;;
let unfix (Fix x) = x ;;
 
let yc : 'a 'b. (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
   = fun f -> let g x a = f ((unfix x) x) a in g (fix g) ;;

let f x y = yc (
  fun self (m,n) ->
    if m=0 then n+1
    else if n=0 then self ((m-1), 1)
    else self ((m-1), self (m, (n-1)))
) (x,y) ;;

(* Til' the next time nerds. *)
