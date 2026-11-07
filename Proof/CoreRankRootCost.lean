import DoubleEmbeddedEdgePrice
import DominatingBlueEndpoint
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- The total original root shortfall and root/exterior incidences are
controlled by the rank of the selected full core, for this very region. -/
theorem ordinary_core_rank_caps_root_cost (G : SimpleGraph X) (D : ℕ) (K : DegreeRegion G D)
    (cap : ∀v,Nat.card (G.neighborSet v)≤D) :
    D*minimumExposure G D+rootShortfall G K.roots D+crossCount G K.roots K.rest≤
      2*matchingEdges (G.induce K.core) := by
  have caps := positive_selection_caps G K.barrier K.tight K.pieces D
    (fun c _ => (K.critical c).1) (fun c _ => (K.critical c).2)
    (fun c _ x => (induced_neighbor_count_le (G.induce K.barrierᶜ) c.supp x).trans
      ((induced_neighbor_count_le G K.barrierᶜ x.val).trans (cap _)))
  have dom := positivePieces_dominate G K.barrier K.pieces D
  change edgeSurplus (G.induce K.core) D≤edgeSurplus (G.induce K.positiveCore) D at dom
  have small : K.positiveCore⊆K.core := by
    rintro x ⟨z,rfl,has⟩
    exact ⟨z,rfl,has.1⟩
  let inc : (G.induce K.positiveCore).Copy (G.induce K.core) :=
    ⟨⟨fun z => ⟨z.val,small z.property⟩,fun e => e⟩,fun _ _ eq => Subtype.ext (congrArg (fun z : ↥K.core => z.val) eq)⟩
  have ranked : edgeSurplus (G.induce K.positiveCore) D≤(matchingEdges (G.induce K.positiveCore):ℤ) := caps.2.2
  have le : (matchingEdges (G.induce K.positiveCore):ℤ)≤matchingEdges (G.induce K.core) := by
    exact_mod_cast rank_le_of_copy inc
  have w := K.weight_identity cap
  have out : (D:ℤ)*(minimumExposure G D:ℤ)+(rootShortfall G K.roots D:ℤ)+(crossCount G K.roots K.rest:ℤ)≤
      2*(matchingEdges (G.induce K.core):ℤ) := by omega
  exact_mod_cast out

#print axioms ordinary_core_rank_caps_root_cost
end JSP452Audit.StarHost
