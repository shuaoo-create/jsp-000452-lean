import Lean.Elab.Tactic.Omega

/- Local counting for the padded (g,f)-factor reduction in factor-from-tutte.md.
   Slots and tokens that occur in a matching are counted here; realizing these
   counts by edges of the auxiliary graph is a separate graph-level obligation. -/
namespace JSP452Audit

def localPadding (d redCap : Nat) : Nat := 1 + (redCap - d)
def slotCount (d redCap : Nat) : Nat := d + localPadding d redCap
def mustCount (d redCap : Nat) : Nat := slotCount d redCap - redCap
def mayCount (d redCap blueCap : Nat) : Nat := redCap + blueCap - d

theorem nonemptyLocalSides (d a : Nat) :
    0 < slotCount d a ∧ 0 < mustCount d a := by
  unfold mustCount slotCount localPadding
  omega

theorem totalTokenCount (d a b : Nat) (cap : d ≤ a+b) :
    mustCount d a + mayCount d a b = b + localPadding d a := by
  unfold mustCount slotCount mayCount localPadding
  omega

def localDeviation (d a b k : Nat) : Nat := (k-a) + (d-k-b)

theorem localUnmatchedLower (d a b k mandatoryUsed optionalUsed : Nat)
    (cap : d ≤ a+b)
    (hm : mandatoryUsed ≤ mustCount d a) (ho : optionalUsed ≤ mayCount d a b)
    (hs : k+mandatoryUsed+optionalUsed ≤ slotCount d a) :
    localDeviation d a b k ≤
      (mustCount d a - mandatoryUsed) +
      (slotCount d a - (k+mandatoryUsed+optionalUsed)) := by
  unfold mustCount slotCount mayCount localDeviation localPadding at *
  omega

def greedyMust (d a k : Nat) : Nat :=
  min (mustCount d a) (slotCount d a - k)
def greedyMay (d a b k : Nat) : Nat :=
  min (mayCount d a b) (slotCount d a - k - greedyMust d a k)

theorem greedyAttainsLocalDeviation (d a b k : Nat)
    (cap : d ≤ a+b) (hk : k ≤ d) :
    greedyMust d a k ≤ mustCount d a ∧
    greedyMay d a b k ≤ mayCount d a b ∧
    k + greedyMust d a k + greedyMay d a b k ≤ slotCount d a ∧
    (mustCount d a - greedyMust d a k) +
      (slotCount d a - (k+greedyMust d a k+greedyMay d a b k)) =
      localDeviation d a b k := by
  unfold greedyMay greedyMust mustCount slotCount mayCount localPadding localDeviation
  omega

#print axioms localUnmatchedLower
#print axioms greedyAttainsLocalDeviation
end JSP452Audit
