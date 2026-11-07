import RegularIndependentReserve

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Every nonempty independent cut in a zero-reserve regular critical host
makes each nonnegative term of the existing reserve identity vanish. -/
theorem zero_reserve_independent_cut [Nonempty X] (Q : SimpleGraph X) (D : ℕ)
    (pos : 0<D) (reg : ∀x,Nat.card (Q.neighborSet x)=D)
    (crit : PerfectAfterEveryDeletion Q) (zero : baseReserve Q D=0)
    (I : Set X) (present : I.Nonempty) (indep : Q.IsIndepSet I) :
    baseReserve (Q.induce Iᶜ) D=0 ∧
      matchingEdges (Q.induce Iᶜ)+I.ncard=matchingEdges Q+1 ∧
      ∀ j, 1≤j → j<D → savedAt Q I j=0 ∧
        deletionBudget Q j=I.ncard+deletionBudget (Q.induce Iᶜ) j := by
  have step : D-1+1=D := by omega
  have regular : ∀x,Nat.card (Q.neighborSet x)=D-1+1 := by simpa only [step] using reg
  have balance := regular_independent_reserve Q (D-1) regular crit I present indep
  dsimp only at balance
  rw [step,zero] at balance
  have lower := factorCritical_cut_rank Q crit I present
  have noSum : ∑ j∈Finset.range (D-1),savedAt Q I (j+1)=0 := by omega
  refine ⟨by omega,by omega,?_⟩
  intro j positive small
  have mem : j-1∈Finset.range (D-1) := Finset.mem_range.mpr (by omega)
  have one := Finset.single_le_sum (fun k _ => Nat.zero_le (savedAt Q I (k+1))) mem
  rw [noSum,show j-1+1=j from by omega] at one
  have saved : savedAt Q I j=0 := Nat.eq_zero_of_le_zero one
  refine ⟨saved,?_⟩
  have bound := deletion_le_after_cut_add Q I j
  dsimp [savedAt] at saved
  omega

/-- After any nonempty cut from a factor-critical host, a real maximum
matching covers every remaining vertex still of full degree D. The cut need
not be independent and the remainder is allowed to be empty. -/
theorem factorCritical_cut_covering_maximum (Q : SimpleGraph X) (D : ℕ)
    (pos : 0<D) (cap : ∀x,Nat.card (Q.neighborSet x)≤D)
    (crit : PerfectAfterEveryDeletion Q) (I : Set X) (present : I.Nonempty) :
    minimumExposure (Q.induce Iᶜ) D=0 ∧
      ∃ M : (Q.induce Iᶜ).Subgraph, M.IsMatching ∧
        M.edgeSet.ncard=matchingEdges (Q.induce Iᶜ) ∧
        ∀x,Nat.card ((Q.induce Iᶜ).neighborSet x)=D → x∈M.verts := by
  have bound (x : ↥(Iᶜ : Set X)) : Nat.card ((Q.induce Iᶜ).neighborSet x)≤D :=
    (induced_neighbor_count_le Q Iᶜ x).trans (cap x.val)
  have budget := factorCritical_top_budget_after_nonempty_cut Q D pos cap crit I present
  have exposure := (deletionBudget_zero_iff_minimumExposure_zero (Q.induce Iᶜ) D pos bound).mp budget
  refine ⟨exposure,?_⟩
  obtain ⟨M,hm,max,att⟩ := minimumExposure_attained (Q.induce Iᶜ) D
  have empty : exposedFull (Q.induce Iᶜ) M D=∅ := (Set.ncard_eq_zero (s := exposedFull (Q.induce Iᶜ) M D)).mp (att.trans exposure)
  refine ⟨M,hm,max,?_⟩
  intro x full
  by_contra absent
  have mem : x∈exposedFull (Q.induce Iᶜ) M D := ⟨absent,full⟩
  rw [empty] at mem
  exact mem

#print axioms zero_reserve_independent_cut
#print axioms factorCritical_cut_covering_maximum
end JSP452Audit.StarHost
