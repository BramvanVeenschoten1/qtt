(*
Funny ideas:
  first:
    core,
    elab,
    norm,
    convert,
    environment,
    variable update:
      EITHER substitute env, term, outtype
      OR     keep unify-list

  elaboration:
    1 lift letrecs to fixpoints
    2 lift holes to postulates
    3 implicit arguments
    4 nested patterns
    5 equations
    6 translate to eliminators?
        delete mutual recursion?
*)

(* some impredicative encodings for propositions *)

let Bottom = Pi A : Type, A

let Not (A : Type) : Type = A -> Bottom

let Top : Type = Not Bottom

let trivial : Top = fun x -> x

let double_negate_intro (A : Type)(x : A) : Not (Not A) = fun f -> f x

let triple_negate_elim (A : Type)(f : Not (Not (Not A))): Not A = fun x -> f (double_negate_intro A x)

(* The Identity type *)

let Id (A : Type)(x : A)(y : A) : Type = Pi P : A -> Type, P x -> P y

let refl (A : Type)(x : A): Id A x x = fun _ px -> px

let replace (A : Type)(x : A)(y : A)(eq : Id A x y): Pi P : A -> Type, P x -> P y = eq

let sym (A : Type)(x : A)(y : A)(eq : Id A x y): Id A y x = eq (fun z -> Id A z x) (refl A x)

let trans (A : Type)(x : A)(y : A)(z : A)(eq0 : Id A x y)(eq1 : Id A y z): Id A x z = eq1 (Id A x) eq0

let cong (A : Type)(B : Type)(x : A)(y : A)(f : A -> B)(eq : Id A x y): Id B (f x)(f y) = eq (fun z -> Id B (f x)(f z)) (refl B (f x))

(* Identity for Type *)

let TId (A : Type)(B : Type): Type = Pi F : Type -> Type, F A -> F B

let TRefl (A : Type): TId A A = fun _ fa -> fa

let TReplace (A : Type)(B : Type)(eq : TId A B): Pi F : Type -> Type, F A -> F B = eq

let TSym (A : Type)(B : Type)(eq : TId A B): TId B A = eq (fun z -> TId z A) (TRefl A)

let TTrans (A : Type)(B : Type)(C : Type)(eq0 : TId A B)(eq1 : TId B C): TId A C = eq1 (TId A) eq0

let TCong (A : Type)(B : Type)(F : Type -> Type)(eq : TId A B): TId (F A) (F B) = eq (fun D -> TId (F A) (F D)) (TRefl (F A))

let TCast (A : Type)(B : Type)(eq : TId A B): A -> B = eq (fun x -> x)

let TLift (A : Type)(x : A)(y : A)(P : A -> Type)(eq : Id A x y): TId (P x)(P y) = eq (fun z -> TId (P x) (P z)) (TRefl (P x))

(* bool *)

type bool
| true
| false

let lift (b : bool) : Type =
  match b with
  | true -> Top
  | false -> Bottom

(* Nat *)

type Nat
| zero
| succ (1 Nat)

let rec nat_inductive (0 P : Nat -> Type)(pz : P zero)(ps : Pi n : Nat, P n -> P (succ n))(n : Nat): P n =
  match n with
  | zero -> pz
  | succ m -> ps m (nat_inductive m)

let rec plus (n : Nat)(m : nat): Nat = 
  match n with
  | zero -> m
  | succ n -> succ (plus m n)

let rec less (n : Nat)(m : Nat): bool =
  match m with
  | zero -> false
  | succ m -> leq n m
and leq (n : Nat)(m : Nat): bool =
  match n with
  | zero -> true
  | succ n -> less n m

let Less n m = lift (less n m)

let rec eq (n : Nat)(m : Nat): bool =
  match n with
  | zero -> (match m with
    | zero -> true
    | succ m -> false)
  | succ n -> (match m with
    | zero -> false
    | succ m -> eq n m)

let rec dec_eq(n : Nat)(m : Nat)(eq : lift (eq n m)): Id Nat n m =
  match n with
  | zero -> (match m with
    | zero -> refl Nat zero
    | (succ m) -> eq (Id Nat n m))
  | (succ n) -> (match m with
    | zero ->  eq (Id Nat n m)
    | (succ m) -> cong Nat n m succ (dec_eq n m eq))

(* List *)

type List (A : Type)
| nil
| cons (1 A) (1 List)

let rec foldl (0 A : Type)(0 B : Type)(f : A -> B -> B)(1 acc : B)(1 xs : List A): B =
  match xs with
  | nil -> acc
  | cons x xs -> foldl A B f (f x acc) xs

let rec foldr (0 A : Type)(0 B : Type)(f : A -> B -> B)(1 acc : B)(1 xs : List A): B =
  match xs with
  | nil -> acc
  | cons x xs -> f x (foldr A B f acc xs)

let reverse (0 A : Type)(xs : List A): List A =
  foldl A (List A) (cons A) (nil A) xs

let length(0 A : Type)(xs : List A): Nat =
  foldr A Nat (fun _ -> succ) zero xs

let append(0 A : Type)(xs : List A)(ys : List A): List A =
  foldr A (List A) (cons A) ys xs

let rec nth (0 A : Type)(n : Nat)(xs : List A)(le : Less n (length xs)): A =
  match xs with
  | nil -> le A
  | cons x xs -> match n with
    | zero -> x
    | succ n -> nth A n xs le

let rec append_length (0 A : Type)(xs : List A)(ys : List A): Id Nat (plus (length A xs)(length A ys)) (length (append A xs ys)) =
  match xs with
  | nil -> refl Nat (length ys)
  | cons x xs -> cong Nat Nat (plus (length A xs)(length A ys)) (length (append A xs ys)) succ (append_length A xs ys)

(* Exercise *)

val fold_dual :
  Pi 0 A : Type,
  Pi 0 B : Type,
  Pi f : A -> B -> B,
  Pi acc : B,
  Pi xs : List A,
  Id B
    (foldr A B f acc xs)
    (foldl A B f acc (reverse xs))

let fold_dual2
  (0 A : Type)
  (0 B : Type)
  (f : A -> B -> B)
  (acc : B)
  (xs : List A):
    Id b
      (foldr A B f acc xs)
      (foldl A B f acc (reverse xs))
  = fold_dual A B f acc xs

(* Either *)

type Either (A : Type)(B : Type)
| Left  (1 A)
| Right (1 B)

(* And *)

type And (A : Type)(B : Type)
| mk (1 A) (1 B)
