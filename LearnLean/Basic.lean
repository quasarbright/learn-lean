def hello := "world"

-- following the learn tutorial for functional programming
-- https://lean-lang.org/functional_programming_in_lean/

-- defining structures
structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := { x := 0, y := 0}

#eval ({x := 1, y := 2} : Point)
-- #check {x := 1, y := 2} error. no generic record types

structure Point3D where
  x : Float
  y : Float
  z : Float
deriving Repr

def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0 }

-- #check (origin3D : Point) error. nominal subtyping?

-- record spread
def add1x (p : Point) : Point := { p with x := p.x + 1}

-- constructors
#check Point.mk
#check (Point.mk)

-- shorthand for defining argument types
def add (x y : Nat) : Nat := x + y

-- infix of type/static methods
-- called "accessor dot notation"
#eval "Hello, ".append "world"
-- "Hello, " has type String, so it turns into
-- String.append "Hello, " "world"


-- defining a type method
def Point.scale (k : Float) (p : Point) : Point := {
  x := k*p.x,
  y := k*p.y,
}

-- can use accessor even though the point isn't the first arg
#eval ({ x := 1, y := 2} : Point).scale 2
-- field accessors use this infix
#check Point.x
#eval (Point.x origin)

-- inductive types
-- inductive Nat where
--   | zero : Nat
--   | succ (n : Nat) : Nat

-- pattern matching
def isZero (n : Nat) : Bool :=
  match n with
  -- note the qualified case name
  -- for built in Nat
  | Nat.zero => true
  | Nat.succ _ => false

-- detects non-termination
-- def evenLoops (n : Nat) : Bool :=
--   match n with
--   | Nat.zero => true
--   | Nat.succ k => not (evenLoops n)
--   --                 should be k ^
-- obviously this means some valid terminating programs are rejected

-- polymorphic types
structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero }

-- type as an argument
def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

-- you have to explicitly pass it in
#eval replaceX Nat natOrigin 1

inductive Sign where
  | pos
  | neg

-- dependent type
def posOrNegThree (s : Sign) : match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)

-- not normalized
#check posOrNegThree Sign.pos
#check posOrNegThree Sign.neg

-- lists
def nums : List Nat := [1,2,3]

def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | List.nil => Nat.zero
  | List.cons _ ys => Nat.succ (length α ys)

def lengthFancy (α : Type) (xs : List α) : Nat :=
  match xs with
  | [] => Nat.zero
  | _ :: ys => Nat.succ (length α ys)

-- inferred type argument
def replaceXInferred {α} (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }
#eval replaceXInferred natOrigin 5


-- Maybe is called Option with none and some
-- suffix ? is used for functions that return option
#check List.head?
-- fancy stuff
#check List.head!
-- weird error
-- #eval List.head! []

-- tuples
#check ((1, true) : Nat × Bool)
#check ((1, true) : Prod Nat Bool)
#check ({ fst := 1, snd := true} : Prod Nat Bool)
#check (1, True, "hello")
#check Prod

-- unions (discriminated)
#check Sum.inl 1
-- \oplus
#check (Sum.inl 1 : Nat ⊕ Bool)

-- unit
#eval Unit.unit
#eval ()
#check (() : Unit)
-- #check (() : ()) error bc it thinks it's the value

-- don't match on pairs
-- def sameLength (xs : List α) (ys : List β) : Bool :=
--   match (xs, ys) with
--   | ([], []) => true
--   | (x :: xs', y :: ys') => sameLength xs' ys'
--   | _ => false
-- use simultaneous pattern matching instead
def sameLength (xs : List α) (ys : List β) : Bool :=
  match xs, ys with
  | [], [] => true
  | _ :: xs', _ :: ys' => sameLength xs' ys'
  | _,_ => false

def lastElement {a} (as : List a) : Option a :=
  match as with
  | [] => none
  | a::[] => some a
  | _::as => lastElement as

def boolToSum {a} (prod : Bool × a) : a ⊕ a :=
  match prod with
  | (false, a) => Sum.inl a
  | (true, a) => Sum.inr a

def boolToSumDep {a} (prod : Bool × a) : if (Prod.fst prod) then Empty ⊕ a else a ⊕ Empty :=
  match prod with
  -- if you replace an inl with inr, it gives an error!
  | (false, a) => Sum.inl a
  | (true, a) => Sum.inr a

#check boolToSumDep (true, 2)

--fancy matching
def lengthDefMatch : List α → Nat
  | [] => 0
  | _ :: ys => Nat.succ (lengthDefMatch ys)

def drop : Nat → List α → List α
  | Nat.zero, xs => xs
  | _, [] => []
  | Nat.succ n, _ :: xs => drop n xs

def fromOption (default : α) : Option α → α
  | none => default
  | some x => x

-- let
def letExample := let x := 1; x + x

def even : Nat → Bool
  | 0 => true
  -- succ sugar pattern
  | n + 1 => not (even n)

def halve : Nat → Nat
  | 0 => 0
  | 1 => 0
  -- succ succ sugar pattern
  | n + 2 => halve n + 1

-- functions from infix operators
-- use \. or \centerdot, not \cdot
#check (· + 1)

-- namespaces
namespace NewNamespace
def triple (x : Nat) : Nat := 3 * x
def quadruple (x : Nat) : Nat := 2 * x + 2 * x
end NewNamespace

#eval NewNamespace.triple 2

def timesTwelve (x : Nat) :=
  -- local open
  open NewNamespace in
  quadruple (triple x)

-- global open
open NewNamespace in
#check quadruple

-- if let
-- for when you only care about one case of a match
inductive Inline : Type where
  | lineBreak
  | string : String → Inline
  | emph : Inline → Inline
  | strong : Inline → Inline

-- def Inline.string? (inline : Inline) : Option String :=
--   match inline with
--   | Inline.string s => some s
--   | _ => none

def Inline.string? (inline : Inline) : Option String :=
  if let Inline.string s := inline then
    some s
  else none

-- positinonal structure arguments
#eval (⟨1, 2⟩ : Point)

-- string interpolation
#eval s!"three fives is {NewNamespace.triple 5}"

def existsList : Σ x : Type, List x :=
  -- need the angle brackets
  ⟨Nat, [1]⟩
def existsListProd : (x : Type) × List x :=
  ⟨Nat, [1]⟩

def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]

-- statically checked indexing
def hedgehog := woodlandCritters[0]
def deer := woodlandCritters[1]
def snail := woodlandCritters[2]
-- def oops := woodlandCritters[3] -- error at compile time

-- equality proposition
def onePlusOneIsTwo : 1 + 1 = 2 := rfl
-- def onePlusOneIsFifteen : 1 + 1 = 15 := rfl -- type error

-- theorem
def OnePlusOneIsTwo : Prop := 1 + 1 = 2
theorem onePlusOneIsTwoThm : OnePlusOneIsTwo := rfl

-- tactics
theorem onePlusOneIsTwoTactics : 1 + 1 = 2 := by
  decide

-- manual proof
theorem andImpliesOr : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a _ => Or.inl a

theorem onePlusOneAndLessThan : 1 + 1 = 2 ∨ 3 < 5 := by decide
theorem notTwoEqualFive : ¬(1 + 1 = 5) := by decide
theorem trueIsTrue : True := by decide
theorem trueOrFalse : True ∨ False := by decide
theorem falseImpliesTrue : False → True := by decide

-- taking in evidence as an argument
def third (xs : List α) (ok : xs.length > 2) : α := xs[2]

-- automatic evidence proof by tactics
#eval third woodlandCritters (by decide)

-- isTrue is a constructor of Decidable
-- which contains the proposition (implicitly) and its proof
#check isTrue
-- this carries a proof of ¬p
#check isFalse
-- data type indexed on a Prop
#check Decidable

-- indexing without evidence
def thirdOption (xs : List α) : Option α := xs[2]?
#eval thirdOption woodlandCritters

theorem twoPlusThreeIsFive : 2 + 3 = 5 := rfl
-- theorem fiveLtEighteenRfl : 5 < 18 := rfl error bc rfl makes an =, not a <
theorem fiveLtEighteen : 5 < 18 := by simp

-- how does the correspondence work between Bools at value-level and Props at type-level?
#check 5 < 18 -- Prop
#check (5 < 18 : Bool) -- Bool
#check True -- Prop
#check true
-- I guess Props get casted to Bools when used as values?
-- yep
#eval if 5 < 8 then 1 else 2
-- if expects a Bool, but that's a Prop
#eval if (decide (5 < 80)) then 1 else 2
-- lean inserts this decide for you to convert a Prop to a bool by proving it
#check decide

-- the type class of things that support addition
#check Add
#check Add Nat
-- type classes are Type → Type functions?

-- heterogeneous addition
#check HAdd -- no iea what outParam means
-- but it's basically Type → Type → Type → Type ?
-- for left summand, right summand, and output type I think

-- type for nonzero Nats
inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

-- def seven : Pos := 7 -- failed to synthesize OfNat Pos 7
-- couldn't find a type class instance

-- type class
class Plus (α : Type) where
  plus : α → α → α

instance : Plus Nat where
  plus := Nat.add

#eval (Plus.plus 1 2)

def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)

instance : Plus Pos where
  plus := Pos.plus

#check Plus
#check Plus Nat
-- but what _is_ a Plus Nat? The instance?
-- yeah, literally
def myInstance : Plus Pos := {plus := Pos.plus}
#check myInstance.plus
attribute [instance] myInstance -- now this will be used automatically
-- instance : Cls where ... is just sugar on this
-- also, where is just sugar for records!
instance : Plus Pos := {plus := Pos.plus}
-- more sugar
-- structure is sugar for
inductive PointCore
| mk : Nat → Nat → PointCore
namespace PointCore
def x (p : PointCore) : Nat :=
  match p with
  | mk x _ => x

def y (p : PointCore) : Nat :=
  match p with
  | mk _ y => y
end PointCore
-- class is sugar for
structure AddCore (α : Type u) where
  add : α → α → α
attribute [class] AddCore
-- inductive seems to be core
-- attribute tags things like AddCore with information
-- like the fact that it's a class
-- necessary bc it's literally just a Type
-- Nice reflection!
-- TODO how to define your own attributes and do special behaviors?
-- TODO how to define macros like instance (it's not quite a macro I think)

instance : Add Pos where
  add := Pos.plus

-- using + on Pos now
def twoPos := Pos.one + Pos.one

-- overloading number literals
instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n

def eight : Pos := 8
-- def zeroPos : Pos := 0 -- fails to synthesize an instance

inductive Even where
  | zero -- implicit : Even
  | add2 : Even → Even
deriving Repr

def twoEven := Even.zero.add2

def Even.plus (a : Even) (b : Even) : Even :=
  match a with
    | Even.zero => b
    | Even.add2 a' => Even.add2 (a'.plus b)

instance : Add Even where
  add := Even.plus

-- need "inductive" instances of OfNat for Even
instance : OfNat Even 0 where
  ofNat := Even.zero
instance : OfNat Even (n + 2) where
  ofNat :=
    let rec natPlusTwo : Nat → Even
      | 0 => Even.add2 Even.zero
      | n + 1 => Even.add2 (natPlusTwo n)
    natPlusTwo n
#eval (0 : Even)
-- #eval (1 : Even) -- unable to synthesize instance
#eval (2 : Even)
-- #eval (9000 : Even) -- this breaks somewhere between 9000 and 10000

-- instance implicits, like haskell Num a => ...
def List.sumOfContents [Add α] [OfNat α 0] : List α → α
  | [] => 0
  | x :: xs => x + xs.sumOfContents
def fourNats : List Nat := [1, 2, 3, 4]
#eval fourNats.sumOfContents
def fourPos : List Pos := [1, 2, 3, 4]
-- #eval fourPos.sumOfContents -- failed to synthesize bc no 0

-- polymorphic instance which requires type argument instance
instance [Add α] : Add (PPoint α) where
  add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y }

#check OfNat.ofNat

-- left off about to start https://lean-lang.org/functional_programming_in_lean/type-classes/out-params.html
