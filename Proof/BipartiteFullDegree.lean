import NestedClassHall
import PairFamily
import DeletionBudget

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- A nonnegative square matrix with equal positive row and column sums has
a permutation in its positive support. -/
private theorem weighted_hall_permutation [Fintype X] (w : X→X→ℕ) (d : ℕ) (pos : 0<d)
    (row : ∀x,∑y,w x y=d) (col : ∀y,∑x,w x y=d) :
    ∃f : X≃X,∀x,0<w x (f x) := by
  classical
  let nbr (x:X) := Finset.univ.filter (fun y => 0<w x y)
  have hall (T : Finset X) : T.card≤(T.biUnion nbr).card := by
    let S := T.biUnion nbr
    have reduced (x:X) (hx:x∈T) : ∑y∈S,w x y=d := by
      rw [←row x]
      apply Finset.sum_subset (Finset.subset_univ S)
      intro y _ out
      by_contra nonzero
      exact out (Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩⟩)
    have total : ∑x∈T,∑y∈S,w x y=T.card*d := by
      exact (Finset.sum_congr rfl reduced).trans (by simp)
    have bound (y:X) : ∑x∈T,w x y≤d := by
      rw [←col y]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) (by intros;omega)
    have upper := Finset.sum_le_sum (s:=S) (fun y _ => bound y)
    rw [←Finset.sum_comm,total] at upper
    simp only [Finset.sum_const,nsmul_eq_mul] at upper
    by_contra! smaller
    have strict := Nat.mul_lt_mul_of_pos_right (show S.card<T.card from smaller) pos
    exact (not_lt_of_ge (show T.card*d≤S.card*d from upper)) strict
  obtain ⟨f,inj,legal⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' nbr).mp hall
  exact ⟨Equiv.ofBijective f ⟨inj,Finite.surjective_of_injective inj⟩,fun x => (Finset.mem_filter.mp (legal x)).2⟩

/-- A matching in a finite bipartite graph covers all vertices attaining the
degree bound, on both sides simultaneously. -/
theorem bipartite_full_degree_matching (G : SimpleGraph X) (L : Set X) (d : ℕ)
    (pos : 0<d) (cap : ∀x,Nat.card (G.neighborSet x)≤d)
    (bip : ∀a b,G.Adj a b → (a∈L ↔ b∉L)) :
    ∃M : G.Subgraph,M.IsMatching ∧ ∀v,Nat.card (G.neighborSet v)=d → v∈M.verts := by
  classical
  let _ := Fintype.ofFinite X
  let n (v:X) := Nat.card (G.neighborSet v)
  let w (v u:X) := (if G.Adj v u then 1 else 0)+(if u=v then d-n v else 0)
  have row (v:X) : ∑u,w v u=d := by
    have sum : (∑u:X,if G.Adj v u then 1 else 0)=n v := by
      rw [←Finset.sum_filter]
      simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
      let S := Finset.univ.filter (fun u => G.Adj v u)
      have same : (S : Set X)=G.neighborSet v := by ext u;simp [S]
      change S.card=Nat.card (G.neighborSet v)
      rw [←Set.ncard_coe_finset,same,Nat.card_coe_set_eq]
    change ∑u,((if G.Adj v u then 1 else 0)+(if u=v then d-n v else 0))=d
    rw [Finset.sum_add_distrib,sum]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
    have le : n v≤d := cap v
    omega
  have sym (v u:X) : w v u=w u v := by
    by_cases eq : v=u
    · subst u;rfl
    · simp [w,eq,Ne.symm eq,G.adj_comm]
  have col (u:X) : ∑v,w v u=d := by simpa only [fun v => sym v u] using row u
  obtain ⟨f,legal⟩ := weighted_hall_permutation w d pos row col
  have moves {v:X} (full : n v=d) : f v≠v := by
    intro eq
    have h := legal v
    simp [w,eq,full] at h
  have edge {v:X} (ne : f v≠v) : G.Adj v (f v) := by
    by_contra no
    have h := legal v
    simp [w,ne,no] at h
  let T := {v : X | v∈L ∧ f v≠v}
  let l : T ↪ X := ⟨Subtype.val,Subtype.val_injective⟩
  let r : T ↪ X := ⟨fun v => f v.val, fun _ _ h => Subtype.ext (f.injective h)⟩
  have linked (v:T) : G.Adj (l v) (r v) := edge v.property.2
  have dis : Disjoint (Set.range l) (Set.range r) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨v,rfl⟩ ⟨u,eq⟩
    exact (bip (l u) (r u) (linked u)).mp u.property.1 (eq.symm ▸ v.property.1)
  let M := JSP452Audit.Padded.pairFamily G l r linked
  have matching := JSP452Audit.Padded.pairFamily_isMatching G l r linked dis
  refine ⟨M,matching,?_⟩
  intro v full
  change v∈Set.range l ∪ Set.range r
  by_cases inside : v∈L
  · exact Or.inl ⟨⟨v,inside,moves full⟩,rfl⟩
  obtain ⟨u,hu⟩ := f.surjective v
  have ne : f u≠u := by
    intro fix
    have uv : u=v := fix.symm.trans hu
    exact moves full (uv ▸ fix)
  have ul : u∈L := (bip u (f u) (edge ne)).mpr (hu.symm ▸ inside)
  exact Or.inr ⟨⟨u,ul,ne⟩,hu⟩

#print axioms bipartite_full_degree_matching
end JSP452Audit.StarHost
