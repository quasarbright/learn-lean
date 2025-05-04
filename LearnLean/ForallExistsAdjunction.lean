-- analogous to the isomorphism between pairs and functions,
-- there is an isomorphism between existentials and universals
-- where existentials are dependent pairs
-- and universals are dependent functions
def dependentCurry
  {A : Type}
  {B : A -> Type}
  (abc : (a : A) × B a -> C)
  : (a' : A) -> (B a' -> C)
  := fun a => fun b => abc (Sigma.mk a b)

def dependentUncurry
  {A : Type}
  {B : A -> Type}
  (abc : (a' : A) -> (B a' -> C))
  : ((a : A) × (B a)) -> C
  := fun ab => abc (Sigma.fst ab) (Sigma.snd ab)
