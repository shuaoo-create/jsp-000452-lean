import SixDegreeLimitedSaturatedWeight
namespace JSP452Audit.StarHost
open SimpleGraph

theorem full_roots_of_zero_shortfall {X:Type*} [Finite X] (G:SimpleGraph X) (S:Set X)
    (D:ℕ) (cap:∀v,Nat.card (G.neighborSet v)≤D) (zero:rootShortfall G S D=0) :
    ∀x∈S,Nat.card (G.neighborSet x)=D := by
  classical
  intro x mem
  by_contra diff
  have lt : Nat.card (G.neighborSet x)<D := lt_of_le_of_ne (cap x) diff
  have gap := Finset.sum_lt_sum (s:=S.toFinite.toFinset) (f:=fun v => Nat.card (G.neighborSet v))
    (g:=fun _ => D) (fun v _ => cap v) ⟨x,S.toFinite.mem_toFinset.mpr mem,lt⟩
  have card : S.toFinite.toFinset.card=S.ncard := by rw [←Set.ncard_coe_finset,S.toFinite.coe_toFinset]
  rw [Finset.sum_const,card,nsmul_eq_mul,Nat.mul_comm] at gap
  change originalDegreeSum G S<D*S.ncard at gap
  change D*S.ncard-originalDegreeSum G S=0 at zero
  omega

theorem zero_loss_full_closed_region {X:Type*} [Finite X] {G:SimpleGraph X} {D:ℕ}
    (K:DegreeRegion G D) (cap:∀v,Nat.card (G.neighborSet v)≤D)
    (zero:rootShortfall G K.roots D=0) (boundary:crossCount G K.roots K.rest=0) :
    let W := K.core∪K.roots
    (∀v∈W,∀w,G.Adj v w → w∈W) ∧ (∀v∈W,Nat.card (G.neighborSet v)=D) ∧
    W.ncard=2*(matchingEdges (G.induce K.core)+K.roots.ncard)+minimumExposure G D := by
  intro W
  have roots := full_roots_of_zero_shortfall G K.roots D cap zero
  refine ⟨?_,?_,?_⟩
  · intro v mem w edge
    rcases mem with hc|hr
    · rcases regionCore_neighbor G K.barrier K.pieces hc edge with rw|cw
      · exact Or.inr rw
      · exact Or.inl cw
    · by_contra outside
      have rest : w∈K.rest := fun mem => outside (mem.elim Or.inr Or.inl)
      exact no_edge_when_port_zero G boundary hr rest edge
  · intro v mem
    exact mem.elim (fun hc => regionCore_full_degree G K.barrier K.pieces D K.full hc) (fun hr => roots v hr)
  · change (K.core∪K.roots).ncard=_
    rw [Set.ncard_union_eq (region_partition G K.barrier K.pieces).1.symm,K.core_order]
    change 2*matchingEdges (G.induce K.core)+K.roots.ncard+minimumExposure G D+K.roots.ncard=2*(matchingEdges (G.induce K.core)+K.roots.ncard)+minimumExposure G D
    omega

#print axioms full_roots_of_zero_shortfall
#print axioms zero_loss_full_closed_region
end JSP452Audit.StarHost
