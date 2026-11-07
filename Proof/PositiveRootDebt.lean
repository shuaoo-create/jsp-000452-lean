import DegreeRegion
import PositiveWeightDomination
namespace JSP452Audit.StarHost
open SimpleGraph
namespace DegreeRegion
variable {X : Type*} [Finite X] {G : SimpleGraph X} {D : ℕ} (r : DegreeRegion G D)
abbrev positive := positivePieces G r.barrier r.pieces D
abbrev positiveCore := regionCore G r.barrier r.positive

theorem positive_caps (cap : ∀ x, Nat.card (G.neighborSet x)≤D) :
    let H := G.induce r.positiveCore
    2*edgeSurplus H D ≤ (D:ℤ)*r.positive.ncard ∧ (D:ℤ)*r.positive.ncard ≤ 2*(matchingEdges H:ℤ) ∧
      edgeSurplus H D ≤ matchingEdges H := by
  apply positive_selection_caps G r.barrier r.tight r.pieces D (fun c _ => (r.critical c).1) (fun c _ => (r.critical c).2)
  intro c _ x
  exact (induced_neighbor_count_le (G.induce r.barrierᶜ) c.supp x).trans
    ((induced_neighbor_count_le G r.barrierᶜ x.val).trans (cap _))

/-- A positive full-degree deficit creates actual positive pieces, and their
total surplus pays for the root shortfall, the internal root edges and the top column. -/
theorem root_debt (cap : ∀ x, Nat.card (G.neighborSet x)≤D) (lambda : ℕ)
    (width : lambda ≤ minimumExposure G D) :
    (rootShortfall G r.roots D:ℤ) + ((G.induce r.roots).edgeSet.ncard:ℤ) + lambda ≤
    2*edgeSurplus (G.induce r.positiveCore) D - ((D:ℤ)-1)*(minimumExposure G D:ℤ) := by
  have id := r.weight_identity cap
  have pos := positivePieces_dominate G r.barrier r.pieces D
  change edgeSurplus (G.induce r.core) D ≤ edgeSurplus (G.induce r.positiveCore) D at pos
  have tax : (lambda:ℤ) ≤ (minimumExposure G D:ℤ) := by exact_mod_cast width
  rw [sub_mul,one_mul]
  omega

theorem positive_surplus_of_exposure (cap : ∀ x, Nat.card (G.neighborSet x)≤D)
    (high : 0<D) (miss : 0<minimumExposure G D) : 0<edgeSurplus (G.induce r.positiveCore) D := by
  have id := r.weight_identity cap
  have dom := positivePieces_dominate G r.barrier r.pieces D
  change edgeSurplus (G.induce r.core) D ≤ edgeSurplus (G.induce r.positiveCore) D at dom
  have prod : 0 < (D:ℤ)*(minimumExposure G D:ℤ) := mul_pos (by exact_mod_cast high) (by exact_mod_cast miss)
  omega
end DegreeRegion
#print axioms DegreeRegion.positive_caps
#print axioms DegreeRegion.root_debt
#print axioms DegreeRegion.positive_surplus_of_exposure
end JSP452Audit.StarHost