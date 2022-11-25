
(* The idea of storing many values in a single arbitrary precision
   integer is not new. It's been used to prove that, for example,
   Minsky machines with two unbounded registers are Turing complete. *)

(* PROBLEM A *)

(* Let me walk you through my reasoning in a language better than OCaml.
   Let's convert all the numbers to their decimal representation:

    10⊥⍣¯1¨2831 273
┌───────┬─────┐
│2 8 3 1│2 7 3│
└───────┴─────┘
   
   Turn them into a matrix:

    {⌽↑⌽¨10⊥⍣¯1¨⍵}2831 273
2 8 3 1
0 2 7 3

   Concatenate rows and enlist:

    {∊,⌿⌽↑⌽¨10⊥⍣¯1¨⍵}2831 273
2 0 8 2 3 7 1 3

   Turn whatever we've got into a number:

    {⍎∊⍕¨∊,⌿⌽↑⌽¨10⊥⍣¯1¨⍵}2831 273
20823713
 *)

(* No explicit type specifications. I use an IDE, it has a revolutionary feature
   of being able to peek what type something is. *)

let fusion (x, y) =
   let rec helper(x, y, accum) =
     if x = 0 && y = 0 then accum
     else helper(x / 10, y / 10, accum) * 100 + (x mod 10) * 10 + (y mod 10)
   in helper(x, y, 0) ;;

let fission (x) =
   let rec helper(x, aX, aY) =
     if x = 0 then (aX, aY)
     else match helper(x / 100, aX, aY) with
       | (a, b) -> (a * 10 + (x mod 100) / 10, b * 10 + x mod 10)
   in helper(x, 0, 0) ;;

(* PROBLEM B *)

(* I think that you expected students to write code bad enough to bail out on
   numbers of odd length? My solution works for all numbers :).
   Proof: *)

let rec check (x) =
   if x > 10000000 then 1 
   else if fusion(fission x) <> x then 1 / 0
   else check (x + 1)
   ;;

(* This will error if fusion(fission x) <> x. If, on the other hand, you were meaning
   to maybe ask a trick question involving machine integer range:
   # fussion(fission max_int) = max_int
   - bool = true *)

(* PROBLEM C *)

(* Well that's trivial. Just encode absolute values and encode 1/0 at the end as
   a "sign bit". *)

let fusion_int (x, y) =
   let fix (a) = if a < 0 then (-a) * 10 + 1 else a * 10 in
   fusion(fix x, fix y) ;;

let fission_int (x) =
   let unfix (a) = if a mod 10 = 1 then (-a / 10) else a / 10 in
   match fission x with
   | (a, b) -> (unfix a, unfix b) ;;

(* PROBLEM D *)

(* Same thing again. *)

let fusion3 (x, y, z) =
   let fix (a) = if a < 0 then (-a) * 10 + 1 else a * 10 in
   let fusion (x, y) =
      let rec helper(x, y, z, accum) =
        if x = 0 && y = 0 && z = 0 then accum
        else helper(x / 10, y / 10, z / 10, accum) * 1000 + (x mod 10) * 100 + (y mod 10) * 10 + (z mod 10)
      in helper(x, y, 0)
   in
   fusion(fix x, fix y, fix z) ;;

let fission3 (x) =
   let unfix (a) = if a mod 10 = 1 then (-a / 10) else a / 10 in
   let fission (x) =
      let rec helper(x, aX, aY, aZ) =
        if x = 0 then (aX, aY, aZ)
        else match helper(x / 1000, aX, aY, aZ) with
          | (a, b, c) -> (a * 10 + (x mod 1000) / 100, b * 10 + (x mod 100) / 10, c * 10 + x mod 10)
      in helper(x, 0, 0, 0)
   in
   match fission x with
   | (a, b, c) -> (unfix a, unfix b, unfix c) ;;

(* PROBLEM E *)

(* fusion3 is not a function from (c) ;)
   it won't work in some cases, the last 3 digits encode the sign bits, so everything smaller
   than 1000 won't work. *)

(* PROBLEM F *)

(* OCaml is a statically typed language, which makes it useless for solving
   little and funny problems like these. You can't have a function generic on a tuple
   size. If you asked for a list as input i'd probably try translating the APL solution.
   that said, you can just easily adapt my code above. *)

(* PROBLEM G *)

(* IDEA 1:
   If the numbers exhibited some degree of correlation in small contexts, we could
   use the Move-to-front transform. Local correlation then gets encoded to small
   values, which e.g. plays well with some encoding schemes, like Rice-Golomb encoding
   that expects Laplacian (two-sided geometric) distribution.
   In reality numbers don't exhibit local corelation that much :).
   Also, to implement it I'd realistically need lists and that's not allowed as far as I know.
   
   IDEA 2:
   Alphabet reordering. Swap the most commonly occuring number and 0, 2nd most commonly
   occuring to 1, etc... - this assumes that the data does not have an uniform
   distribution.
   
   Of course the last two ideas fail if the data has no local correlation and the digits
   are uniforly distributed. *)

(* An implementation of IDEA 1. *)
(* Step 1: count 1, 2, and 3 digits in the number. *)
let g_count x =
   let rec helper(n, n1, n2, n3) =
     if n = 0 then (n1, n2, n3)
     else if (n mod 10) = 1 then helper(n / 10, n1 + 1, n2, n3)
     else if (n mod 10) = 2 then helper(n / 10, n1, n2 + 1, n3)
     else if (n mod 10) = 3 then helper(n / 10, n1, n2, n3 + 1)
     else helper(n / 10, n1, n2, n3)
   in helper(x, 0, 0, 0) ;;

(* Step 2: replace digit 1 with d1, digit 2 with d2, etc... *)
let g_permute x d1 d2 d3 =
   let rec helper(n, accum) =
     if n = 0 then accum
     else if (n mod 10) = 1 then helper(n / 10, accum) * 10 + d1
     else if (n mod 10) = 2 then helper(n / 10, accum) * 10 + d2
     else if (n mod 10) = 3 then helper(n / 10, accum) * 10 + d3
     else helper(n / 10, accum) * 10 + n mod 10
   in helper(x, 0) ;;

(* Step 3: encode the number. *)
let reduce x =
   let (n1, n2, n3) = g_count x in
        if n1 >= n2 && n2 >= n3             then (g_permute x 1 2 3) * 100+11
   else if n1 <= n2 && n2 <= n3             then (g_permute x 3 2 1) * 100+12
   else if n1 >= n2 && n2 <= n3 && n1 <= n3 then (g_permute x 3 1 2) * 100+21
   else if n1 >= n2 && n2 <= n3 && n1 >= n3 then (g_permute x 1 3 2) * 100+22
   else if n1 <= n2 && n2 >= n3 && n1 <= n3 then (g_permute x 2 3 1) * 100+13
   else if n1 <= n2 && n2 >= n3 && n1 >= n3 then (g_permute x 2 1 3) * 100+31
   else 1 / 0 ;;

(* Step 4: decode the number. *)
let unreduce x =
   let (n, v) = (x / 100, x mod 100)
in   if v = 11 then g_permute n 1 2 3 
else if v = 12 then g_permute n 3 2 1
else if v = 21 then g_permute n 3 1 2
else if v = 22 then g_permute n 1 3 2
else if v = 13 then g_permute n 2 3 1
else if v = 31 then g_permute n 2 1 3
else 1 / 0
;;
