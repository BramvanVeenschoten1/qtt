
(* Some basic types *)

type unit
| tt : unit

let unit_irrelevant(0 x : unit): unit = tt

type Void

let void_irrelevant(0 x : Void): Void = match0 x with

type Pair (A : Type)(B : Type)
| mk : A -o B -o Pair A B

type Maybe(A : Type)
| Nothing : Maybe A
| Just : A -o Maybe A

(* This should not pass the positivity checker
type Neg
| mk : (Neg -> Void) -> Neg

let omega : Neg -> Void =
  fun x -> match x with | mk y -> y x

let Omega : Void = omega (mk omega)
*)

(* Identity *)

let Id (0 A : Type)(0 x : A)(0 y : A) : Type = Pi P : A -> Type, P x -> P y

let refl (0 A : Type)(0 x : A): Id A x x = fun _ px -> px

let sym (0 A : Type)(0 x : A)(0 y : A)(eq : Id A x y): Id A y x = eq (fun z -> Id A z x) (refl A x)

let trans (0 A : Type)(0 x : A)(0 y : A)(0 z : A)(eq0 : Id A x y)(eq1 : Id A y z): Id A x z = eq1 (Id A x) eq0

let cong (0 A : Type)(0 B : Type)(0 x : A)(0 y : A)(0 f : A -> B)(eq : Id A x y): Id B (f x)(f y) = eq (fun z -> Id B (f x)(f z)) (refl B (f x))

(* contrived example for inductive checker *)

type Foo(A : Type)(B : Type)
| nil : Foo A B
| cons : A => Bar A B -> Foo A B
and Bar(X : Type)(Y : Type)
| nol : Bar X Y
| cins : Y -o Foo X Y -> Bar X Y

(* likewise for termination checker *)

let rec Foo_ind
  (A : Type)
  (B : Type)
  (P : Foo A B -> Type)
  (Q : Bar A B -> Type)
  (pnil : P (nil A B))
  (qnil : Q (nol A B))
  (pcons : Pi 0 x : A, Pi xs : Bar A B, Q xs -> P (cons A B x xs))
  (qcons : Pi x : B, Pi xs : Foo A B, P xs -> Q (cins A B x xs))
  (xs : Foo A B):
    P xs =
  match xs return P with
  | nil -> pnil
  | cons x xs -> pcons x xs (bar_ind A B P Q pnil qnil pcons qcons xs)
and bar_ind
  (A : Type)
  (B : Type)
  (P : Foo A B -> Type)
  (Q : Bar A B -> Type)
  (pnil : P (nil A B))
  (qnil : Q (nol A B))
  (pcons : Pi 0 x : A, Pi xs : Bar A B, Q xs -> P (cons A B x xs))
  (qcons : Pi x : B, Pi xs : Foo A B, P xs -> Q (cins A B x xs))
  (xs : Bar A B):
    Q xs =
  match xs return Q with
  | nol -> qnil
  | cins x xs -> qcons x xs (Foo_ind A B P Q pnil qnil pcons qcons xs)

(* bool *)

type bool
| true  : bool
| false : bool

let lift (b : bool) : Type =
  match b with
  | true -> unit
  | false -> Void

let distinct (eq : Id bool true false): Void =
  eq lift tt

(* Nat *)

type Nat
| zero : Nat
| succ : Nat -o Nat

let rec nat_inductive (0 P : Nat -> Type)(pz : P zero)(ps : Pi n : Nat, P n -> P (succ n))(n : Nat): P n =
  match n return P with
  | zero -> pz
  | succ m -> ps m (nat_inductive P pz ps m)

let rec plus (n : Nat)(m : Nat): Nat = 
  match n with
  | zero -> m
  | succ n -> succ (plus n m)

let rec eq (n : Nat)(m : Nat): bool =
  match n with
  | zero -> (match m with
    | zero -> true
    | succ m -> false)
  | succ n -> (match m with
    | zero -> false
    | succ m -> eq n m)

let NatEq (n : Nat)(m : Nat): Type = lift (eq n m)

let rec dec_eq(n : Nat)(m : Nat): NatEq n m => Id Nat n m =
  match n return fun (x : Nat) -> NatEq x m => Id Nat x m with
  | zero -> (match m return fun (y : Nat) -> NatEq zero y => Id Nat zero y with
    | zero -> fun _ -> refl Nat zero
    | succ m -> fun p -> (match0 p with))
  | succ n -> (match m return fun (y : Nat) -> NatEq (succ n) y => Id Nat (succ n) y with
    | zero -> fun p -> (match0 p with)
    | succ m -> fun p -> cong Nat Nat n m succ (dec_eq n m p))

(* dec_eq equations, equations not implemented
let rec dec_eq: Pi n : Nat, Pi m : Nat, lift (eq n m) => Id Nat n m
| zero     zero     _ -> refl Nat zero
| (succ n) (succ m) p -> dec_eq n m p
| _        _        p -> (match0 p with)
*)


(* Needed for irrelevance of identities, can be replaced by indexed types or builtin equality *)
val id_irrelevant: Pi 0 A : Type, Pi 0 x : A, Pi 0 y : A, Id A x y => Id A x y 

let elim_neq(0 n : Nat)(0 m : Nat)(0 eq : NatEq n m): Id Nat n m =
  id_irrelevant Nat n m (dec_eq n m eq)

let unit_equal : Pi 0 x : unit, Pi 0 y : unit, Id unit x y =
  fun (0 x) -> match0 x return fun (x : unit) -> Pi 0 y : unit, Id unit x y with
  | tt -> fun (0 y) -> match0 y return fun (y : unit) -> Id unit tt y with
    | tt -> refl unit tt

let rec nat_uip(n : Nat)(m : Nat): Pi 0 x : NatEq n m, Pi 0 y : NatEq n m, Id (NatEq n m) x y =
  match n return fun (i : Nat) -> Pi 0 x : NatEq i m, Pi 0 y : NatEq i m, Id (NatEq i m) x y with
  | zero -> (match m return fun (j : Nat) -> Pi 0 x : NatEq zero j, Pi 0 y : NatEq zero j, Id (NatEq zero j) x y with
    | zero -> unit_equal
    | succ m -> fun (0 x) (0 _) -> (match0 x with))
  | succ n -> (match m return fun (j : Nat)  -> Pi 0 x : NatEq (succ n) j, Pi 0 y : NatEq (succ n) j, Id (NatEq (succ n) j) x y with
    | zero -> fun (0 x) (0 _) -> (match0 x with)
    | succ m -> nat_uip n m)
  
(* List *)

type List (A : Type)
| nil : List A
| cons : A -o List A -o List A

let rec list_ind (0 A : Type)(0 P : List A -> Type)(pnil : P (nil A))(pcons : Pi x : A, Pi xs : List A, P xs -> P (cons A x xs))(xs : List A): P xs =
  match xs return P with
  | nil -> pnil
  | cons x xs -> pcons x xs (list_ind A P pnil pcons xs)

let rec foldr (0 A : Type)(0 B : Type)(f : A -o B -o B)(1 acc : B)(1 xs : List A): B =
  match1 xs with
  | nil -> acc
  | cons x xs -> f x (foldr A B f acc xs)

let rec foldl (0 A : Type)(0 B : Type)(f : A -o B -o B)(1 acc : B)(1 xs : List A): B =
 match1 xs with
 | nil -> acc
 | cons x xs -> foldl A B f (f x acc) xs

let reverse(0 A : Type): List A -o List A =
  foldl A (List A) (cons A) (nil A)

let rec length(0 A : Type)(xs : List A): Nat =
  match xs with
  | nil -> zero
  | cons _ xs -> succ (length A xs)

let append(0 A : Type)(1 xs : List A)(1 ys : List A): List A =
  foldr A (List A) (cons A) ys xs

(* len (xs ++ ys) = len xs + len ys *)

(* proof by dependent pattern matching *)
let rec append_length (0 A : Type)(xs : List A)(ys : List A): Id Nat (plus (length A xs)(length A ys)) (length A (append A xs ys)) =
  match xs return fun (zs : List A) -> Id Nat (plus (length A zs)(length A ys))(length A (append A zs ys)) with 
  | nil -> refl Nat (length A ys)
  | cons _ xs -> cong Nat Nat (plus (length A xs)(length A ys)) (length A (append A xs ys)) succ (append_length A xs ys)

(* proof by induction principle *)
let append_length2  (0 A : Type)(xs : List A)  (ys : List A): Id Nat (plus (length A xs)(length A ys)) (length A (append A xs ys)) =
  let len = length A in
  let app = append A in
  list_ind A
    (fun (zs : List A) -> Id Nat (plus (len zs)(len ys))(len (app zs ys)))
    (refl Nat (len ys))
    (fun x xs ih -> cong Nat Nat (plus (len xs)(len ys))(len (app xs ys)) succ ih)
    xs

(* Build n-ary lists *)

let rec NaryType(A : Type)(n : Nat): Type =
  match n with
  | zero -> List A
  | succ n -> A -> NaryType A n

let rec NaryImp(A : Type)(n : Nat)(xs : List A): NaryType A n =
  match n return NaryType A with
  | zero -> reverse A xs
  | succ n -> fun x -> NaryImp A n (cons A x xs)

let MakeList (A : Type)(n : Nat): NaryType A n =
  NaryImp A n (nil A)

let threeBools : List bool = MakeList bool (succ (succ (succ zero))) true false true

(* inbounds list access *)

(* list with external bounds constraint *)

let rec Less(n : Nat)(m : Nat): Type =
  match m with
  | zero -> Void
  | succ m ->
    match n with
    | zero -> unit
    | succ n -> Less n m

let less_than_zero = fun (n : Nat) ->
  match n return fun (m : Nat) -> Less m zero => Void with
  | zero -> void_irrelevant
  | succ n -> void_irrelevant

let rec nth_1 (0 A : Type)(n : Nat)(xs : List A): Less n (length A xs) => A =
  match xs return fun (zs : List A) -> Less n (length A zs) => A  with
  | nil -> fun le -> (match0 less_than_zero n le with)
  | cons x xs -> match n return fun (m : Nat) -> Less m (succ (length A xs)) => A with
    | zero -> fun _ -> x
    | succ n -> nth_1 A n xs
    
(* Vec By large elimination *)

let rec Vec_0 (A : Type)(n : Nat): Type =
  match n with
  | zero -> unit
  | succ n -> Pair A (Vec_0 A n)

let rec Fin_0 (n : Nat): Type =
  match n with
  | zero -> Void
  | succ n -> Maybe (Fin_0 n)

(* having only one reachable branch, the match on n should be erasable *)
let rec nth_2 (0 A : Type)(n : Nat): Vec_0 A n -> Fin_0 n -> A =
  match n return fun (m : Nat) -> Vec_0 A m -> Fin_0 m -> A with
  | zero -> fun xs i -> (match0 i with)
  | succ n -> fun xs i ->
    match xs with
    | mk x xs ->
      match i with
      | Nothing -> x
      | Just i -> nth_2 A n xs i

(* Vec by second-class indexed types *)

type Vec_1 (A : Type)(n : Nat)
| nil : NatEq n zero => Vec_1 A n
| cons : Pi 0 m : Nat, A -o Vec_1 A m -o NatEq n (succ m) => Vec_1 A n

type Fin_1(n : Nat)
| fzero : Pi 0 m : Nat, NatEq n (succ m) => Fin_1 n
| fsucc : Pi 0 m : Nat, Fin_1 m -o NatEq n (succ m) => Fin_1 n

let fin_zero_empty(x : Fin_1 zero): Void =
  let f (0 m : Nat)(0 eq : NatEq zero (succ m)): Void =
    elim_neq zero (succ m) eq (fun x -> match x with | zero -> unit | succ _ -> Void) tt
  in
  match x with
  | fzero m eq -> f m eq
  | fsucc m _ eq -> f m eq

let rec nth_3 (0 A : Type)(0 n : Nat)(xs : Vec_1 A n)(i : Fin_1 n): A =
  match xs with
  | nil eq0 -> (match0 fin_zero_empty (elim_neq n zero eq0 Fin_1 i) with)
  | cons m0 x xs eq0 -> match i with
    | fzero m1 eq1 -> x
    | fsucc m1 i eq1 ->
      nth_3 A m0 xs (elim_neq m1 m0 (elim_neq n (succ m1) eq1 (fun z -> NatEq z (succ m0)) eq0) Fin_1 i)
 
(* Accessible *)

type Acc(A : Type)(R : A -> A -> Type)(x : A)
| mk : (Pi y : A, R y x -> Acc A R y) -> Acc A R x

let rec acc_irrelevant(0 A : Type)(0 R : A -> A -> Type)(0 x : A)(0 acc : Acc A R x): Acc A R x =
  match0 acc with
  | mk f -> mk A R x (fun y le -> acc_irrelevant A R y (f y le))

