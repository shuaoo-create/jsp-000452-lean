import TightHalfCutHasClosedSupport
namespace JSP452Audit.StarHost
open SimpleGraph

theorem degrees_full_at_saturated_sum {X:Type*} [Finite X] (G:SimpleGraph X) (D:ℕ) (S:Set X)
    (cap:∀x∈S,Nat.card (G.neighborSet x)≤D) (sat:originalDegreeSum G S=D*S.ncard) :
    ∀x∈S,Nat.card (G.neighborSet x)=D := by
  classical
  intro x hx
  by_contra ne
  have less := lt_of_le_of_ne (cap x hx) ne
  have sum := Finset.sum_lt_sum (s:=S.toFinite.toFinset) (g:=fun _ => D)
    (fun x mem => cap x (S.toFinite.mem_toFinset.mp mem)) ⟨x,S.toFinite.mem_toFinset.mpr hx,less⟩
  have card : S.toFinite.toFinset.card=S.ncard := by rw [←Set.ncard_coe_finset,S.toFinite.coe_toFinset]
  rw [Finset.sum_const,nsmul_eq_mul,Nat.cast_id,card,Nat.mul_comm] at sum
  change originalDegreeSum G S<D*S.ncard at sum
  omega

theorem tight_cut_roots_have_full_degree {X:Type*} [Finite X] (G:SimpleGraph X)
    (D:ℕ) (cap:∀v,Nat.card (G.neighborSet v)≤D) (S T:Set X) (dis:Disjoint S T)
    (sat:crossCount G (S∪T)ᶜ (S∪T)+2*crossCount G T S=D*S.ncard+D*T.ncard) :
    (∀x∈S∪T,Nat.card (G.neighborSet x)=D) ∧
      (G.induce S).edgeSet.ncard=0 ∧ (G.induce T).edgeSet.ncard=0 := by
  let O := (S∪T)ᶜ
  have so : Disjoint S O := disjoint_compl_right.mono_left Set.subset_union_left
  have tO : Disjoint T O := disjoint_compl_right.mono_left Set.subset_union_right
  have all : S∪T∪O=Set.univ := Set.union_compl_self _
  have ds := partition_handshake G S T O dis so tO all
  have dt := partition_handshake G T S O dis.symm tO so (by rw [Set.union_comm T S];exact all)
  have payS := degree_sum_le_cap G S D (fun x _ => cap x)
  have payT := degree_sum_le_cap G T D (fun x _ => cap x)
  change crossCount G O (S∪T)+2*crossCount G T S=D*S.ncard+D*T.ncard at sat
  rw [cut_cross_union_right G O S T dis,crossCount_swap G O S,crossCount_swap G O T] at sat
  rw [crossCount_swap G S T] at ds
  have fullS := degrees_full_at_saturated_sum G D S (fun x _ => cap x) (by omega)
  have fullT := degrees_full_at_saturated_sum G D T (fun x _ => cap x) (by omega)
  exact ⟨fun x h => h.elim (fullS x) (fullT x),by omega,by omega⟩

#print axioms degrees_full_at_saturated_sum
#print axioms tight_cut_roots_have_full_degree
end JSP452Audit.StarHost
