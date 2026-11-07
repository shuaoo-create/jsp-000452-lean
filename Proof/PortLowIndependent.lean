import GoodPortParts
import CliquePairs
import PairFamily

namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded

variable {X : Type*}

private theorem full_low_apart (Q : SimpleGraph X) (D : ℕ) {x : X}
    (low : x∈portLow Q D) (full : x∈portFull Q D) : False :=
  (Nat.ne_of_lt low) full

private theorem range_labels (A : Set X) : Set.range (Function.Embedding.subtype (·∈A)) = A := by
  ext x; exact ⟨fun ⟨y,e⟩ => e ▸ y.property,fun h => ⟨⟨_,h⟩,rfl⟩⟩

variable [Finite X]

/-- Complete a prescribed matching outside v whenever all its remaining
unmatched vertices other than v lie in a clique. Preserve every old edge. -/
private theorem fill_matched_remainder (Q : SimpleGraph X) (v : X) (K : Q.Subgraph)
    (hm : K.IsMatching) (miss : v∉K.verts) (odd : Odd (Nat.card X))
    (F : Set X) (clique : Q.IsClique F) (rem : ∀ x, x≠v → x∉K.verts → x∈F) :
    ∃ M : Q.Subgraph, M.IsMatching ∧ M.verts = {x | x≠v} ∧ K≤M := by
  let A : Set X := ({v} : Set X)ᶜ
  let B := A \ K.verts
  have sub : K.verts ⊆ A := by
    intro x hx eq; exact miss (Set.mem_singleton_iff.mp eq ▸ hx)
  have total := Set.ncard_sdiff_add_ncard_of_subset sub
  have used := matching_vertices_eq_twice_edges hm
  have sizeA : A.ncard = Nat.card X - 1 := by rw [show A = ({v} : Set X)ᶜ from rfl,Set.ncard_compl,Set.ncard_singleton]
  have even : Even (Nat.card B) := by
    rw [Nat.even_iff,Nat.card_coe_set_eq]
    have par := Nat.odd_iff.mp odd
    change (A \ K.verts).ncard % 2 = 0
    omega
  let inc := Function.Embedding.subtype (·∈B)
  have inF (x : B) : x.val ∈ F := rem x.val (fun h => x.property.1 (Set.mem_singleton_iff.mpr h)) x.property.2
  obtain ⟨T,matchT,vertsT⟩ := existsMatchingOnEvenClique Q inc
    (fun {x y} ne => clique (inF x) (inF y) (fun h => ne (Subtype.ext h))) even
  have usedT : T.verts = B := vertsT.trans (range_labels B)
  have dis : Disjoint K.verts T.verts := by
    rw [usedT]
    exact Set.disjoint_left.mpr (fun _ hx hb => hb.2 hx)
  refine ⟨K⊔T,matching_sup_of_disjoint_verts Q hm matchT dis,?_,le_sup_left⟩
  ext x
  change (x∈K.verts ∨ x∈T.verts) ↔ x≠v
  rw [usedT]
  change (x∈K.verts ∨ x≠v ∧ x∉K.verts) ↔ x≠v
  by_cases h : x∈K.verts
  · exact ⟨fun _ => fun eq => miss (eq ▸ h),fun _ => Or.inl h⟩
  · simp [h]

/-- Expose v and retain the original low edge y--z. Every other low vertex
is assigned its own full partner; all remaining slots are filled in the full clique. -/
theorem matching_keep_low_edge (Q : SimpleGraph X) (D : ℕ) (cap : ∀x, Nat.card (Q.neighborSet x)≤D)
    (clique : Q.IsClique (portFull Q D))
    (joined : ∀ x∈portFull Q D, ∀ y∈portLow Q D, Q.Adj x y)
    (room : (portLow Q D).ncard ≤ (portFull Q D).ncard) (odd : Odd (Nat.card X))
    {y z v : X} (hy : y∈portLow Q D) (hz : z∈portLow Q D) (hv : v∈portLow Q D)
    (vy : v≠y) (vz : v≠z) (yz : Q.Adj y z) :
    ∃ M : Q.Subgraph, M.IsMatching ∧ M.verts = {x | x≠v} ∧ M.Adj y z := by
  classical
  let L : Set X := {x | x∈portLow Q D ∧ x≠y ∧ x≠z ∧ x≠v}
  let F := portFull Q D
  let _ := Fintype.ofFinite L
  let _ := Fintype.ofFinite F
  have enough : L.ncard ≤ F.ncard := (Set.ncard_le_ncard (fun _ h => h.1 : L ⊆ portLow Q D)).trans room
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := L) (β := F)
    (by simpa only [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] using enough)
  let l := Function.Embedding.subtype (·∈L)
  let r := f.trans (Function.Embedding.subtype (·∈F))
  have rFull {x : X} (h : x∈Set.range r) : x∈F := by
    obtain ⟨i,rfl⟩ := h
    exact (f i).property
  have dis : Disjoint (Set.range l) (Set.range r) := by
    rw [show Set.range l=L from range_labels L]
    exact Set.disjoint_left.mpr (fun _ hx hr => full_low_apart Q D hx.1 (rFull hr))
  have cross (i : L) : Q.Adj (l i) (r i) := (joined _ (f i).property _ i.property.1).symm
  let P := pairFamily Q l r cross
  have pairVerts : P.verts = L ∪ Set.range r :=
    (pairFamily_verts Q l r cross).trans (congrArg (· ∪ Set.range r) (range_labels L))
  have matchP := pairFamily_isMatching Q l r cross dis
  let E := Q.subgraphOfAdj yz
  have eVerts : E.verts={y,z} := Q.subgraphOfAdj_verts yz
  have apart : Disjoint E.verts P.verts := by
    rw [eVerts,pairVerts]
    apply Set.disjoint_left.mpr
    intro x hx hp
    rcases hx with eq|eq
    · subst x
      exact hp.elim (fun h => h.2.1 rfl) (fun hr => full_low_apart Q D hy (rFull hr))
    · have same : x=z := eq
      subst x
      exact hp.elim (fun h => h.2.2.1 rfl) (fun hr => full_low_apart Q D hz (rFull hr))
  let K := E⊔P
  have matchK := matching_sup_of_disjoint_verts Q (Subgraph.IsMatching.subgraphOfAdj yz) matchP apart
  have finished : K.verts = {y,z} ∪ (L ∪ Set.range r) := by
    change E.verts ∪ P.verts = _
    rw [eVerts,pairVerts]
  have miss : v∉K.verts := by
    rw [finished]
    rintro ((eq|eq)|(h|hr))
    · exact vy eq
    · exact vz eq
    · exact h.2.2.2 rfl
    · exact full_low_apart Q D hv (rFull hr)
  have rest (x : X) (xv : x≠v) (unused : x∉K.verts) : x∈F := by
    rw [finished] at unused
    by_contra notFull
    have low : x∈portLow Q D := lt_of_le_of_ne (cap x) notFull
    have xy : x≠y := fun eq => unused (Or.inl (Or.inl eq))
    have xz : x≠z := fun eq => unused (Or.inl (Or.inr eq))
    exact unused (Or.inr (Or.inl ⟨low,xy,xz,xv⟩))
  obtain ⟨M,matching,verts,includeK⟩ := fill_matched_remainder Q v K matchK miss odd F clique rest
  exact ⟨M,matching,verts,includeK.2 (Or.inl (Q.subgraphOfAdj_adj_self yz))⟩

/-- No edge can have two low endpoints: a low endpoint has a nonneighbor,
also low because of the join. Exposing that nonneighbor while retaining the
edge contradicts the good-port condition at its other endpoint. -/
theorem portLow_independent (Q : SimpleGraph X) (D : ℕ) (cap : ∀x, Nat.card (Q.neighborSet x)≤D)
    (clique : Q.IsClique (portFull Q D))
    (joined : ∀ x∈portFull Q D, ∀ y∈portLow Q D, Q.Adj x y)
    (room : (portLow Q D).ncard+1≤(portFull Q D).ncard) (odd : Odd (Nat.card X))
    (good : ∀ y∈portLow Q D, GoodPort Q y) : Q.IsIndepSet (portLow Q D) := by
  classical
  intro y hy z hz _ yz
  obtain ⟨w,hw⟩ := (Set.ncard_pos (Set.toFinite (portFull Q D))).mp (by omega)
  have cannot : ¬ ∀ v, v≠z → Q.Adj v z := by
    intro all
    have setEq : Q.neighborSet z = ({z} : Set X)ᶜ := by
      ext v; exact ⟨fun e => (show Q.Adj z v from e).ne.symm,fun h => (all v h).symm⟩
    have bound := Set.ncard_le_ncard (show Q.neighborSet w ⊆ ({w} : Set X)ᶜ from
      fun x h => (show Q.Adj w x from h).ne.symm)
    rw [Set.ncard_compl,Set.ncard_singleton] at bound
    change (Q.neighborSet w).ncard = D at hw
    change (Q.neighborSet z).ncard < D at hz
    rw [setEq,Set.ncard_compl,Set.ncard_singleton] at hz
    omega
  push Not at cannot
  obtain ⟨v,vz,miss⟩ := cannot
  have vy : v≠y := fun eq => miss (eq ▸ yz)
  have lv : v∈portLow Q D := lt_of_le_of_ne (cap v) (fun full => miss (joined v full z hz))
  obtain ⟨M,hm,verts,edge⟩ := matching_keep_low_edge Q D cap clique joined (by omega) odd hy hz lv vy vz yz
  exact miss (good y hy v vy M hm verts z edge)

#print axioms matching_keep_low_edge
#print axioms portLow_independent
end JSP452Audit.StarHost
