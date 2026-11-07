import CrossingBoundaryBudget
import OrdinaryCliquePrice

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X J : Type*} [Finite X] [Fintype J]

/-- Two degree units in the roots are already spent on an internal edge. -/
theorem split_roots_cut_cap (G : SimpleGraph X) (C : J→Set X) (R : Set X) (D : ℕ)
    (apart : ∀ i j, i≠j → Disjoint (C i) (C j)) (outside : ∀ i, C i⊆Rᶜ)
    (closed : ∀ i a, a∈C i → ∀ b, G.Adj a b → b∉C i → b∈R)
    (reg : ∀ x, Nat.card (G.neighborSet x)=D)
    (internal : ∃ a∈R, ∃ b∈R, G.Adj a b) :
    (∑ i,crossCount G (C i) (C i)ᶜ)+2 ≤ R.ncard*D := by
  classical
  let _ := Fintype.ofFinite R
  have each (i : J) : crossCount G (C i) (C i)ᶜ ≤ crossCount G R (C i) := by
    let _ := Fintype.ofFinite (C i)
    rw [crossCount_swap G R (C i),crossCount_eq_neighbor_sum,crossCount_eq_neighbor_sum]
    exact Finset.sum_le_sum (fun x _ => Set.ncard_le_ncard (fun _ h =>
      ⟨h.1,closed i x.val x.property _ h.1 h.2⟩))
  have external := (Finset.sum_le_sum (s:=Finset.univ) (fun i _ => each i)).trans
    (sum_cross_into_disjoint G R Rᶜ C outside apart)
  have total : crossCount G R Rᶜ + crossCount G R R ≤ R.ncard*D := by
    rw [crossCount_eq_neighbor_sum,crossCount_eq_neighbor_sum,←Finset.sum_add_distrib]
    calc
      _ ≤ ∑ _ : R, D := Finset.sum_le_sum (fun v _ => by
        let N := G.neighborSet v.val
        have dis : Disjoint (N∩Rᶜ) (N∩R) := disjoint_compl_left.mono
          Set.inter_subset_right Set.inter_subset_right
        have eq : (N∩Rᶜ)∪(N∩R)=N := by
          rw [←Set.inter_union_distrib_left,Set.compl_union_self,Set.inter_univ]
        change (N∩Rᶜ).ncard+(N∩R).ncard ≤ D
        rw [←Set.ncard_union_eq dis,eq,←Nat.card_coe_set_eq]
        exact (reg v.val).le)
      _ = _ := by simp [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  obtain ⟨a,ha,b,hb,edge⟩ := internal
  let u : R := ⟨a,ha⟩
  let v : R := ⟨b,hb⟩
  have actual : s(u,v) ∈ (G.induce R).edgeSet := edge
  have pos := (Set.ncard_pos (Set.toFinite _)).mpr (show (G.induce R).edgeSet.Nonempty from ⟨_,actual⟩)
  rw [crossCount_self] at total
  omega

private theorem clique_price_id (D n : ℕ) (lo : 2≤n) (hi : n≤D-1) :
    n*(D+1-n)=2*D-2+(n-2)*(D-1-n) := by
  let a := n-2
  let b := D-1-n
  have size : n=a+2 := by dsimp [a];omega
  have gap : D+1-n=b+2 := by dsimp [b];omega
  have degree : D=a+b+3 := by dsimp [a,b];omega
  change n*(D+1-n)=2*D-2+a*b
  rw [gap,size,Nat.add_mul,Nat.mul_add]
  omega

/-- If one of the remaining cliques has at least three vertices, the root
budget forces that clique to have size D−1 and every other part to be a singleton. -/
theorem one_large_split_clique (G : SimpleGraph X) (C : J→Set X) (R : Set X) (D : ℕ)
    (six : 6≤D) (card : R.ncard=Fintype.card J+1)
    (apart : ∀ i j, i≠j → Disjoint (C i) (C j)) (outside : ∀ i, C i⊆Rᶜ)
    (closed : ∀ i a, a∈C i → ∀ b, G.Adj a b → b∉C i → b∈R)
    (reg : ∀ x, Nat.card (G.neighborSet x)=D)
    (internal : ∃ a∈R, ∃ b∈R, G.Adj a b)
    (cl : ∀i, G.IsClique (C i)) (sizes : ∀i, 1≤(C i).ncard ∧ (C i).ncard≤D-1)
    (j : J) (big : 3≤(C j).ncard) :
    (C j).ncard=D-1 ∧ ∀i, i≠j → (C i).ncard=1 := by
  classical
  let f (i:J) := crossCount G (C i) (C i)ᶜ
  let g (i:J) := D+(if i=j then D-2 else 0)
  have cost (i:J) : f i=(C i).ncard*(D+1-(C i).ncard) :=
    clique_boundary_count G (C i) D (cl i) (fun x _ => reg x)
  have cap := split_roots_cut_cap G C R D apart outside closed reg internal
  rw [card,Nat.add_mul,one_mul] at cap
  change (∑i,f i)+2≤Fintype.card J*D+D at cap
  have le (i:J) : g i≤f i := by
    by_cases eq : i=j
    · subst i
      have idn := clique_price_id D (C j).ncard (by omega) (sizes j).2
      simp [g]; rw [cost];omega
    · simp only [g,if_neg eq,add_zero]
      exact clique_boundary_at_least_degree G (C i) D (cl i) (fun x _ => reg x)
        (sizes i).1 (by have h:=(sizes i).2; omega)
  have total : (∑i,g i)=Fintype.card J*D+(D-2) := by
    simp [g,Finset.sum_add_distrib]
  have tight (i:J) : f i=g i := by
    by_contra diff
    have lt : (∑i,g i)<∑i,f i := Finset.sum_lt_sum (fun t _ => le t)
      ⟨i,Finset.mem_univ _,lt_of_le_of_ne (le i) (Ne.symm diff)⟩
    omega
  constructor
  · have payment := tight j
    simp [g] at payment
    rw [cost,clique_price_id D _ (by omega) (sizes j).2] at payment
    have zero : ((C j).ncard-2)*(D-1-(C j).ncard)=0 := by omega
    rcases Nat.mul_eq_zero.mp zero with z|z
    · omega
    · have h := (sizes j).2; omega
  · intro i diff
    by_contra ne
    have two : 2≤(C i).ncard := by have h:=(sizes i).1; omega
    have payment := tight i
    simp only [g,if_neg diff,add_zero] at payment
    rw [cost,clique_price_id D _ two (sizes i).2] at payment
    omega

#print axioms split_roots_cut_cap
#print axioms one_large_split_clique
end JSP452Audit.StarHost
