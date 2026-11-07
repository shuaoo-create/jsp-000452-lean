import PathCycleDissociation
import PathCycleLayerTwo
import ReserveRowBudget

namespace JSP452Audit.StarHost
open SimpleGraph

/-- A path edge is identified uniquely by its smaller original vertex label. -/
theorem path_edge_ncard (n : ℕ) : (pathGraph n).edgeSet.ncard = n-1 := by
  let lo (i : Fin (n-1)) : Fin n := ⟨i.val,by have := i.isLt; omega⟩
  let hi (i : Fin (n-1)) : Fin n := ⟨i.val+1,by have := i.isLt; omega⟩
  let f (i : Fin (n-1)) : (pathGraph n).edgeSet := ⟨s(lo i,hi i),pathGraph_adj.mpr (Or.inl rfl)⟩
  have inj : Function.Injective f := by
    intro i j eq
    have e : s(lo i,hi i) = s(lo j,hi j) := congrArg Subtype.val eq
    rcases Sym2.eq_iff.mp e with ⟨a,_⟩ | ⟨a,b⟩
    · exact Fin.ext (congrArg (fun x : Fin n => x.val) a)
    · have aa := congrArg Fin.val a
      have bb := congrArg Fin.val b
      dsimp only [lo,hi] at aa bb
      omega
  have hit (a b : Fin n) (step : a.val+1=b.val) : ∃ j : Fin (n-1), s(lo j,hi j) = s(a,b) := by
    let j : Fin (n-1) := ⟨a.val,by have := b.isLt; omega⟩
    have eq₁ : lo j = a := Fin.ext rfl
    have eq₂ : hi j = b := Fin.ext step
    exact ⟨j,by rw [eq₁,eq₂]⟩
  have surj : Function.Surjective f := by
    rintro ⟨e,he⟩
    induction e using Sym2.inductionOn with
    | _ a b =>
      rcases pathGraph_adj.mp he with step | step
      · obtain ⟨j,eq⟩ := hit a b step
        exact ⟨j,Subtype.ext eq⟩
      · obtain ⟨j,eq⟩ := hit b a step
        exact ⟨j,Subtype.ext (eq.trans (Sym2.eq_swap))⟩
  have count := Nat.card_congr (Equiv.ofBijective f ⟨inj,surj⟩)
  simpa only [Nat.card_fin, Nat.card_coe_set_eq] using count.symm

/-- For cycles of order at least three, handshaking on the actual indexed
cycle counts precisely n unordered edges. -/
theorem cycle_edge_ncard (n : ℕ) (hn : 3 ≤ n) : (cycleGraph n).edgeSet.ncard = n := by
  obtain ⟨m,eq⟩ := Nat.exists_eq_add_of_le hn
  rw [eq,Nat.add_comm 3 m]
  have handshake := (cycleGraph (m+3)).sum_degrees_eq_twice_card_edges
  simp only [cycleGraph_degree_three_le,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul] at handshake
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  omega

private theorem reserve_zero_account {X : Type*} [Finite X] (G : SimpleGraph X)
    (zero : baseReserve G 2 = 0) :
    G.edgeSet.ncard = matchingEdges G + deletionBudget G 1 + deletionBudget G 2 := by
  have eq := base_reserve_account G 2
  rw [zero] at eq
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.zero_add] at eq
  change matchingEdges G + (deletionBudget G 1 + deletionBudget G 2) = G.edgeSet.ncard at eq
  omega

theorem tight_path_sizes (n : ℕ) (atLeastTwo : 2 ≤ n) (zero : baseReserve (pathGraph n) 2 = 0) :
    n=2 ∨ n=3 ∨ n=4 ∨ n=6 := by
  have edges := reserve_zero_account _ zero
  rw [path_edge_ncard,pathGraph_matchingEdges,path_budget_two_zero] at edges
  have one := path_deletionBudget_one n
  omega

theorem tight_cycle_sizes (n : ℕ) (atLeastThree : 3 ≤ n) (zero : baseReserve (cycleGraph n) 2 = 0) :
    n=3 ∨ n=4 ∨ n=5 ∨ n=7 := by
  have edges := reserve_zero_account _ zero
  rw [cycle_edge_ncard n atLeastThree,cycleGraph_matchingEdges] at edges
  have one := cycle_deletionBudget_one n atLeastThree
  have two := cycle_budget_two_bound n atLeastThree
  omega

#print axioms path_edge_ncard
#print axioms cycle_edge_ncard
#print axioms tight_path_sizes
#print axioms tight_cycle_sizes
end JSP452Audit.StarHost
