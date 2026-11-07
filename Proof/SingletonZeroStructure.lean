import UnpaidPreferredBlock
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

theorem regular_independent_half (Q : SimpleGraph X) (I : Set X) (ind : Q.IsIndepSet I)
    (D : ℕ) (pos : 0<D) (reg : ∀x,Nat.card (Q.neighborSet x)=D) : I.ncard≤Iᶜ.ncard := by
  classical
  let _ := Fintype.ofFinite I
  let _ := Fintype.ofFinite ↥(Iᶜ)
  have all (x : I) : (Q.neighborSet x.val ∩ Iᶜ)=Q.neighborSet x.val := by
    apply Set.inter_eq_left.mpr
    intro y edge inI
    exact ind x.property inI (show Q.Adj x.val y from edge).ne edge
  have count : crossCount Q I Iᶜ=I.ncard*D := by
    rw [crossCount_eq_neighbor_sum]
    have deg (u : X) : (Q.neighborSet u).ncard=D := reg u
    simp only [all,deg,Finset.sum_const, Finset.card_univ, smul_eq_mul,←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have budget : crossCount Q Iᶜ I≤Iᶜ.ncard*D := by
    rw [crossCount_eq_neighbor_sum]
    calc
      _ ≤ ∑ _ : ↥(Iᶜ),D := Finset.sum_le_sum (fun x _ => (Set.ncard_le_ncard Set.inter_subset_left).trans
        (show (Q.neighborSet x.val).ncard≤D from (reg x.val).le))
      _ = _ := by simp [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  rw [crossCount_swap Q Iᶜ I,count] at budget
  exact Nat.le_of_mul_le_mul_right budget pos

private theorem singleton_mate_blocks (H : SimpleGraph X) (N : H.Subgraph) (hm : N.IsMatching)
    (w : X) (hw : w∉N.verts) (small : (mateBlock H N w).ncard<3) :
    mateBlock H N w={w} := by
  have odd := Nat.odd_iff.mp (mateBlock_odd H N hm w hw)
  have one : (mateBlock H N w).ncard=1 := by omega
  obtain ⟨a,eq⟩ := Set.ncard_eq_one.mp one
  have inside := mateBlock_self H N w
  rw [eq,Set.mem_singleton_iff] at inside
  exact eq.trans (congrArg (fun z : X => ({z} : Set X)) inside.symm)

/-- With no exceptional edge and no nontrivial pointed block, the zero
region is the whole matched support and has exactly D vertices. -/
theorem singleton_branch_zero_size (Q : SimpleGraph X) (I : Set X) (ind : Q.IsIndepSet I)
    (largest : ∀S : Set X,Q.IsIndepSet S → S.ncard≤I.ncard) (D : ℕ) (pos : 0<D)
    (reg : ∀x,Nat.card (Q.neighborSet x)=D)
    (N : (Q.induce Iᶜ).Subgraph) (hm : N.IsMatching)
    (max : N.edgeSet.ncard=matchingEdges (Q.induce Iᶜ))
    (gap : N.vertsᶜ.ncard+1=I.ncard) (noEx : exceptionalMateRegion (Q.induce Iᶜ) N=∅)
    (small : ∀w,w∉N.verts → (mateBlock (Q.induce Iᶜ) N w).ncard<3)
    (clZ : (Q.induce Iᶜ).IsClique (zeroMateRegion (Q.induce Iᶜ) N)) :
    N.verts=zeroMateRegion (Q.induce Iᶜ) N ∧ N.verts.ncard=D := by
  classical
  let H := Q.induce Iᶜ
  let Z := zeroMateRegion H N
  have same : N.verts=Z := by
    ext x
    constructor
    · intro used
      rcases mate_classes_cover H N hm x with ⟨w,hw,hx⟩|z|e
      · rw [singleton_mate_blocks H N hm w hw (small w hw),Set.mem_singleton_iff] at hx
        exact (hw (hx ▸ used)).elim
      · exact z
      · exact (noEx ▸ e : x∈(∅ : Set ↥(Iᶜ))).elim
    · rintro ⟨y,xy,_⟩
      exact N.edge_vert xy
  have half := regular_independent_half Q I ind D pos reg
  have nonZ : Z.Nonempty := by
    by_contra absent
    have empty : N.verts=∅ := same.trans (Set.not_nonempty_iff_eq_empty.mp absent)
    rw [empty,Set.compl_empty,Set.ncard_univ,Nat.card_coe_set_eq] at gap
    omega
  let V := ↥(N.vertsᶜ)
  let _ : Fintype V := Fintype.ofFinite V
  let A : Option V → Set ↥(Iᶜ : Set X) | none => Z | some w => {w.val}
  have count : Nat.card (Option V)=I.ncard := by
    rw [Nat.card_eq_fintype_card,Fintype.card_option,←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
    exact gap
  have cover (x : ↥(Iᶜ)) : ∃j,x∈A j := by
    by_cases used : x∈N.verts
    · exact ⟨none,(show x∈Z by rw [←same]; exact used)⟩
    · exact ⟨some ⟨x,used⟩,rfl⟩
  have nonempty : ∀j,(A j).Nonempty := by rintro (_|w); exact nonZ; exact ⟨w.val,rfl⟩
  have clique : ∀j,H.IsClique (A j) := by
    rintro (_|w)
    · exact clZ
    · intro x hx y hy ne
      exact (ne ((Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm)).elim
  have apartZero (w : V) : Disjoint Z ({w.val} : Set _) := by
    apply Set.disjoint_left.mpr
    rintro a hz eq
    have used : a∈N.verts := same ▸ hz
    exact w.property ((Set.mem_singleton_iff.mp eq) ▸ used)
  have apart : ∀i j,i≠j → Disjoint (A i) (A j) := by
    rintro (_|w) (_|u) ne
    · exact (ne rfl).elim
    · exact apartZero u
    · exact (apartZero w).symm
    · apply Set.disjoint_left.mpr
      rintro a h k
      exact ne (congrArg some (Subtype.ext ((Set.mem_singleton_iff.mp h).symm.trans (Set.mem_singleton_iff.mp k))))
  have outside (w : V) (z) (hz : z∈Z) : ¬H.Adj z w.val := by
    obtain ⟨y,_,none,_⟩ := hz
    exact none w.val w.property
  have sep : ∀i j,i≠j → ∀a∈A i,∀b∈A j,¬H.Adj a b := by
    rintro (_|w) (_|u) ne a ha b hb edge
    · exact ne rfl
    · exact outside u a ha ((Set.mem_singleton_iff.mp hb) ▸ edge)
    · exact outside w b hb ((Set.mem_singleton_iff.mp ha) ▸ edge.symm)
    · have ba := Set.mem_singleton_iff.mp ha
      have bb := Set.mem_singleton_iff.mp hb
      exact u.property (missed_neighbors_subset H N hm max w.property ((ba ▸ bb ▸ edge : H.Adj w.val u.val)))
  have sizes := original_detached_clique_sizes Q I ind largest D reg A count nonempty clique cover apart sep none
  have alt : Z.ncard=1 ∨ Z.ncard=D := sizes
  have parity := matching_vertices_eq_twice_edges hm
  exact ⟨same,by rw [same] at parity ⊢; omega⟩

#print axioms singleton_branch_zero_size
end JSP452Audit.StarHost
