import ThreeByThree
import CoreComponentSum
import PortedComponentAlternatives
namespace JSP452Audit.StarHost
open SimpleGraph

private theorem allocate_bounded_sum {J : Type*} [Fintype J] (cap : J→ℕ) (n : ℕ)
    (room : n≤∑j,cap j) : ∃f:J→ℕ,(∀j,f j≤cap j) ∧ (∑j,f j)=n := by
  classical
  suffices aux : ∀T:Finset J,∀k≤∑j∈T,cap j,∃f:J→ℕ,(∀j,f j≤cap j) ∧ (∑j∈T,f j)=k from aux _ n room
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro k hk
    simp at hk
    exact ⟨fun _ => 0,fun _ => Nat.zero_le _,by simp [hk]⟩
  | @insert a T fresh ih =>
    intro k hk
    rw [Finset.sum_insert fresh] at hk
    obtain ⟨f,bound,eq⟩ := ih (k-cap a) (by omega)
    let g (j:J) := if j=a then min k (cap a) else f j
    have sum : (∑j∈T,g j)=k-cap a := by
      rw [←eq];apply Finset.sum_congr rfl
      intro j hj
      have ne : j≠a := fun h => fresh (h ▸ hj)
      exact if_neg ne
    refine ⟨g,fun j => ?_,?_⟩
    · by_cases same : j=a
      · simp [g,same]
      · simpa [g,same] using bound j
    · rw [Finset.sum_insert fresh,sum];simp only [g,if_true];omega

/-- Select exactly twice n original labels, with an even number in each
connected component. The half-deletion charge sums to n. -/
theorem region_even_deletion_set {X : Type*} [Finite X] (H : SimpleGraph X)
    [Fintype H.ConnectedComponent] (crit : ∀c:H.ConnectedComponent,PerfectAfterEveryDeletion c.toSimpleGraph)
    (n : ℕ) (room : n≤matchingEdges H) :
    ∃U : Set X,U.ncard=2*n ∧ (∑c:H.ConnectedComponent,(c.supp∩U).ncard/2)=n := by
  classical
  have total := (component_rank_budget_gluing H).1
  obtain ⟨f,cap,sum⟩ := allocate_bounded_sum (fun c:H.ConnectedComponent => matchingEdges c.toSimpleGraph) n (total ▸ room)
  have pick (c:H.ConnectedComponent) : ∃L:Set X,L⊆c.supp ∧ L.ncard=2*f c := by
    have ord := factorCritical_order_rank c.toSimpleGraph (crit c) c.nonempty_supp.to_subtype.some
    change Nat.card c.supp=2*matchingEdges c.toSimpleGraph+1 at ord
    rw [Nat.card_coe_set_eq] at ord
    apply Set.exists_subset_card_eq
    have bound := cap c
    omega
  choose L sub sizes using pick
  let U := ⋃c,L c
  have apart : Pairwise (Function.onFun Disjoint L) := by
    intro a b ne
    apply Set.disjoint_left.mpr
    intro v va vb
    have av : H.connectedComponentMk v=a := sub a va
    have bv : H.connectedComponentMk v=b := sub b vb
    exact ne (av.symm.trans bv)
  have size : U.ncard=2*n := by
    change (⋃c,L c).ncard=_
    rw [Set.ncard_iUnion_of_finite (fun c => Set.toFinite (L c)) apart,finsum_eq_sum_of_fintype]
    simp_rw [sizes];rw [←Finset.mul_sum,sum]
  have eq (c:H.ConnectedComponent) : c.supp∩U=L c := by
    ext v
    constructor
    · rintro ⟨hc,inside⟩
      obtain ⟨e,ve⟩ := Set.mem_iUnion.mp inside
      have same : e=c := (show H.connectedComponentMk v=e from sub e ve).symm.trans hc
      exact same ▸ ve
    · exact fun vL => ⟨sub c vL,Set.mem_iUnion.mpr ⟨c,vL⟩⟩
  refine ⟨U,size,?_⟩
  simp_rw [eq,sizes]
  simpa using sum

#print axioms region_even_deletion_set
end JSP452Audit.StarHost
