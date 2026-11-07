import CoreCounts
import CoreIdentity
import CutFees
import ChooseParity

namespace JSP452Audit.Padded
open SimpleGraph

variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

/-- Tight components of the original complement whose A-weight plus incident
edges to T is odd; there is no auxiliary vertex or pool bit in the test. -/
noncomputable def Spec.originalTightOdd (S T : Set V) : Set (P.CoreComponent S T) := by
  classical
  exact {C | P.coreTight C ∧
    let _ := Fintype.ofFinite C.supp
    Odd ((∑ u : C.supp, P.A u.val.val) + P.toCoreCount C)}

/-- Integer cut deficit, evaluated on the original graph and its two caps. -/
noncomputable def Spec.cutDeficit (S T : Set V) : ℤ := by
  classical
  let _ := Fintype.ofFinite S
  let _ := Fintype.ofFinite T
  exact (↑(P.originalTightOdd S T).ncard : ℤ) + ↑(P.cutCrossTS S T) -
    ↑(∑ v : S, P.A v.val) - ↑(∑ v : T, P.B v.val)

@[simp] theorem Spec.cutDeficit_withPoolBit (b : Bool) (S T : Set V) :
    (P.withPoolBit b).cutDeficit S T = P.cutDeficit S T := rfl

/-- Under the admissibility hypothesis tightness means equality of the two
total color allowances with the original degree, vertex by vertex. -/
theorem Spec.coreTight_iff_degree {S T : Set V} (C : P.CoreComponent S T)
    (caps : ∀ v, P.G.degree v ≤ P.A v + P.B v) :
    P.coreTight C ↔ ∀ u : C.supp, P.G.degree u.val.val = P.A u.val.val + P.B u.val.val := by
  constructor
  · intro tight u
    have eq := tight u.val u.property
    unfold Spec.optionalCount at eq
    have bound := caps u.val.val
    omega
  · intro deg u hu
    have eq : P.G.degree u.val = P.A u.val + P.B u.val := deg ⟨u,hu⟩
    change P.A u.val + P.B u.val - P.G.degree u.val = 0
    omega

theorem Spec.originalTightOdd_eq (S T : Set V) (caps : ∀ v, P.G.degree v ≤ P.A v + P.B v) :
    P.originalTightOdd S T = P.tightOdd S T := by
  classical
  ext C
  let _ := Fintype.ofFinite C.supp
  change (P.coreTight C ∧ Odd ((∑ u : C.supp, P.A u.val.val) + P.toCoreCount C)) ↔
    (P.coreTight C ∧ Odd (Nat.card {z : P.Vertex // P.onCore C z}))
  exact and_congr_right fun tight => (P.core_tight_odd_iff C caps tight).symm

/-- Original edge and component counts exactly match the signed canonical
account for either choice of the auxiliary parity. -/
theorem Spec.cutDeficit_eq_canonical (S T : Set V)
    (caps : ∀ v, P.G.degree v ≤ P.A v + P.B v) :
    P.cutDeficit S T = (Nat.card (P.SingletonIndex S T) : ℤ) +
      ↑(P.tightOdd S T).ncard - ↑(Nat.card {z : P.Vertex // ¬ P.keptBy S T z}) := by
  classical
  let _ := Fintype.ofFinite S
  let _ := Fintype.ofFinite T
  dsimp only [Spec.cutDeficit]
  rw [P.originalTightOdd_eq S T caps]
  have fees := P.canonical_cut_fees S T caps
  omega

#print axioms Spec.cutDeficit_withPoolBit
#print axioms Spec.coreTight_iff_degree
#print axioms Spec.originalTightOdd_eq
#print axioms Spec.cutDeficit_eq_canonical
end JSP452Audit.Padded
