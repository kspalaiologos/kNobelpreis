
(* But before we continue with today's show... I would really like to
   greet the person who wrote kNobel Log C. That was very funny and on-spot.
   Not to mention the writing skills :).
   
   As a foreword to this kNobel exercise: Church encoding is rather familiar
   for me, because as you might know from the previous problem, I am unexplainably
   attracted to combinators.
   In fact, with the "prev" problem you gave me an opportunity to talk about them,
   so prepare to be bored to death.
   
   PS: check out https://github.com/kspalaiologos/blc-mb & https://github.com/kspalaiologos/ski-windows
   
   I noticed that you really hate double semicolons, so I had omitted them in this
   solution. I don't test my entries too thoroughly and usually spend around an hour
   on kNobel sheets which might bite me back at some point or another. We will see. *)

(* PROBLEM 1A *)
(* A number N can be encoded using Church encoding as N-fold composition of some function f
   which we receive as the argument of our generating function. *)

let zero = fun f -> fun x -> x
let three = fun f -> fun x -> f (f (f x))

(* PROBLEM 1B *)
(* Converting a church numeral to an integer is simple: Just pass the successor function
   as f! *)

let codeToInt code = code (fun x -> x + 1) 0

(* Converting an integer to a church numeral is more sophisticated. We will need a
   successor function. *)
let rec intToCode x = let succ x = fun f a -> f(x f a) in if x = 0 then zero else succ (intToCode (x - 1))

(* PROBLEM 1C *)
(* The successor function will just apply f one more time. *)
let succ x = fun f a -> f(x f a)

(* Adding church numerals boils down to composing them (apply f m times, then n times). *)
let add x y = fun f a -> x f (y f a)

(* Multiplication is simply repeated addition - add x, y times. *)
let mul x y = fun f a -> x (y f) a

(* Exponentiation is applying function x to the y-th "power".
   This is slightly unintuitive at first. Notice how we partially
   apply x as the functional argument to y. Every composition of f in y
   is then "replaced" with existing church numeral x. Then we apply
   f to it once again. *)
let exp x y = fun f a -> (y x) f a

(* The predecessor function will likely be the hardest to explain :).
   When we apply to the Church numeral n, our function f is called n times.
   As such, we need a strategy to apply the function n-1 times.
   I will implement an auxiliary device: The SKI calculus K combinator
   (Kestrel; called "const" in Haskell) and the I combinator.

   As for more combinator lore, notice that SKK/SKS and I are
   functionally equivalent. This means that just the SK system would be sound!
   In fact, we could make do with a single iota combinator (I think invented
   by Chris Baker), where ix = xSK.
   Later on in the solution we stumble upon an encoding for boolean numbers,
   which is also doable using the SK basis: Define Txy=x and Fxy=y and notice how
   T=K and F=SK... but more about that later :). *)
let pred x =
   let const = fun a u -> a in
   let id = fun a -> a in
   let wrap = fun f g h -> h (g f) in
   fun f a -> (x (wrap f) (const a)) id

(* That's a lot to unpack. Let's step back for a second.
   What we try to accomplish here is to wrap the church numeral
   and use a special function that always ignores its other argument
   to effectively decrement it, and then unwrap the numeral back.
   Notice how "fun f a -> (x (wrap f) (fun f -> f a)) id" is essentially
   an identity function for Church numbers: our container function can
   be defined as "fun a b -> b a" - that is, applies its arguments in reverse
   order. We can of course undo that shall we pass the identity function as "b",
   which we do in both examples.
   
   Notice how (fun f -> f a) is the Church numeral for one. If we keep "wrap"ping it,
   we get the same Church numeral that needs to be unwrapped back again, however, if
   we use "const", the wrapped number ends up being one smaller than the input.
   
   Why so? I'm glad you asked.
   (x (wrap f) (fun f -> f a)) id
      = ((fun a b -> b a) (x f a)) id
      = (fun a b -> b a) (x f a) id
      = id (x f a)
      = x f a
   
   But wait! What about the "const" case? Well.
   (x (wrap f) (const a)) id
      = ((fun a b -> b a) ((x - 1) f a)) id
      = (fun a b -> b a) ((x - 1) f a) id
      = id ((x - 1) f a)
      = (x - 1) f a
   
   An easy way to observe the difference yourself:
      (wrap (fun f -> f a)) id
      = ((fun g h -> h (g f)) (fun f -> f a)) id
      = (fun g -> id (g f)) (fun f -> f a)
      = (fun g -> g f) (fun f -> f a)
      = (fun f -> f a)
      
      (wrap (const a)) id
      = ((fun g h -> h (g f)) ((fun a u -> a) a)) id
      = ((fun g h -> h (g f)) (fun u -> a)) id
      = (fun g h -> h (g f)) (fun u -> a) id
      = (fun g -> id (g f)) (fun u -> a)
      = (fun g -> g f) (fun u -> a)
      = a *)

(* Iter is obviously going to be rather simple. *)
(* We desire the same behaviour as:
   let rec iter f n x = if n < 1 then x else iter f (n - 1) (f x)
   Which is actually pretty easy, because church numerals /ARE/ "iter"! *)

let iter f n x = n f x

(* PROBLEM 2 *)
(* Let's implement Mogensen-Scott encoding (kinda)! *)
(* This works the exact way as the previous encoding, except we
   encode lists in a funny Lisp-y cons/nil format, e.g. [1;2;3]
   becomes (c 1 (c 2 (c 3 nil))).
   It's obvious to notice how cons works here, a bit more interesting
   piece is append, but notice how we can implement it by replacing
   the nil in one list with the other list.
   `forall' and `codeToList' work in a pretty cute way:
   we can map a function with initial value on a list like this:
      (c 1 (c 2 (c 3 nil)))
   call with c=f and nil=n:
(f 1 (f 2 (f 3 n)))
   Automatic folding! Would you look at that?? *)

let nil = fun c -> fun n -> n
let cons x xs = fun c n -> c x (xs c n)
let app xs ys = fun c n -> xs c (ys c n)
let forall xs p = xs (fun x xs -> (p x) && xs) true
let codeToList code = code (fun x xs -> x :: xs) []
let listToCode list = List.fold_right cons list nil

(* PROBLEM 3 *)
(* > Try finding encodings for other types, like bool, int and pairs. Can all types be encoded this way? *)
(* Yes. All types can be encoded this way per the Scott encoding.
   We can encode booleans as follows: *)

let bt = fun t -> fun f -> t
let bf = fun t -> fun f -> f

(* Okay okay. Wait wait wait!!!
   We can also use combinators to implement the exact same thing!!
   Notice how Txy=x and Fxy=y. Do you see a combinator here?
   T = K and F = SK! There are plenty of... interesting things we could do with that!!
   Negation is a freebie - just swap the order of x and y, so we can just use the C combinator from the BCKW system!
   Furthermore, as you can see the true and false values kinda behave like ifs, so we can easily
   construct e.g. a xor operation boils down to RI(BS(RCB)), where the R combinator is conventionally
   defined as λabc . bca ("Robin", ((S(K(S(KS)K)))((S(K(S((SK)K))))K)) in SK).
   For completeness, I present the following combinators:
   - AND: R(KI)
   - OR: TK, where T is the Thrush combinator CI, so ((S(K(S((SK)K))))K) in SK system.
   - XOR: RI(BS(RCB))
   - NOT: C
   - NAND: B(BC)(R(KI)) - B required for composition of NOT and AND. Alternatively, B(RK)(RCB) could maybe work.
   Anyway! We can also implement them in OCaml! *)

let bnot = fun x -> x bf bt
let bor = fun x y -> x bt y
let band = fun x y -> x y bf
let bxor = fun x y -> x (bnot y) y
let bnand = fun x y -> bnot (band x y) 
      
let boolToCode x = if x then bt else bf
let codeToBool x = x true false

(* Integers can be encoded by using a bijection from naturals to integers, that is: 
   f(x) = x / 2 if x mod 2 = 0
   f(x) = -x / 2 if x mod 2 = 1
   Assuming that / is truncating division.
   Example mappings from integers to naturals:
   -5 -4 -3 -2 -1 0 1 2 3 4 5
      9  7  5  3  1 0 2 4 6 8 10
*)

(* As for the pairs, we could either use Scott encoding, or just flatten them and store them as lists,
   and knowing the type of the pair beforehand we can ascertain the original shape from the raveled pair. *)

(* I think I deserve extra dieters, because my implementation of "prev" is especially elegant,
   furthermore the effort I put into explaining the sacred holy combinator lore to bestow you with the
   intrinsically useful should also be acknowledged. *)

(* Cya nerds-. Akhem. I mean. Have a nice day. *)
