import TheTrueDegreeShortfallAtAllOriginalPortEndpoints
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

def restrictInsideIso {X:Type u} (G:SimpleGraph X) {S U:Set X} (sub:S⊆U) :
    (G.induce U).induce {v:U|v.val∈S} ≃g G.induce S where
  toFun v := ⟨v.val.val,v.property⟩
  invFun v := ⟨⟨v.val,sub v.property⟩,v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

namespace TenPortSupport
variable {X:Type u} [Finite X] {G:SimpleGraph X} {K:TenBlockPartition G} {h:ℕ} (W:TenPortSupport G K h)

theorem seed_sized_sets_fit_internal_rank (cap:∀v,Nat.card (G.neighborSet v)≤10)
    (S:Set X) (sub:S⊆W.support) (one:(G.induce S).edgeSet.ncard≤1) :
    S.ncard+W.targetPorts≤W.rank := by
  let Q := G.induce W.support
  let A:Set W.support := {x|x.val∈S}
  let iso := restrictInsideIso G sub
  have size : A.ncard=S.ncard := Nat.card_congr iso.toEquiv
  have edges : (Q.induce A).edgeSet.ncard=(G.induce S).edgeSet.ncard := Nat.card_congr iso.mapEdgeSet
  have bound (v:W.support) : Nat.card (Q.neighborSet v)≤10 := (induced_neighbor_count_le G W.support v).trans (cap v.val)
  have mono := degree_shortfall_mono Q 10 bound (Set.subset_univ A)
  have hand := degree_sum_complement Q Set.univ
  have nil : originalDegreeSum Q (Set.univ:Set W.support)ᶜ=0 := by simp [originalDegreeSum]
  rw [nil,Nat.add_zero] at hand
  have inside := W.edges
  change Q.edgeSet.ncard+1=5*W.support.ncard at inside
  have total : rootShortfall Q Set.univ 10=2 := by
    rw [rootShortfall,Set.ncard_univ,hand];change 10*W.support.ncard-2*Q.edgeSet.ncard=2;omega
  have paid := charged_set_fits_matching Q A 10 bound (by omega)
  have exactRank := W.portRank
  change W.rank=matchingEdges Q+W.targetPorts at exactRank
  omega

#print axioms seed_sized_sets_fit_internal_rank
end TenPortSupport
#print axioms restrictInsideIso
end JSP452Audit.StarHost
