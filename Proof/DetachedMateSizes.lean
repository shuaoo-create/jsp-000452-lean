import UniqueNoncliqueBlock
import TightCliqueFamily
import ZeroMateRegion
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Equality in the boundary sum applies directly after restoring the
labels of a partition of the complement of a largest independent set. -/
theorem original_detached_clique_sizes {J : Type*} [Fintype J] (Q : SimpleGraph X)
    (I : Set X) (ind : Q.IsIndepSet I) (largest : ∀S : Set X,Q.IsIndepSet S → S.ncard≤I.ncard)
    (D : ℕ) (reg : ∀x,Nat.card (Q.neighborSet x)=D)
    (A : J→Set ↥(Iᶜ : Set X)) (same : Nat.card J=I.ncard)
    (nonempty : ∀i,(A i).Nonempty) (clique : ∀i,(Q.induce Iᶜ).IsClique (A i))
    (cover : ∀x,∃i,x∈A i)
    (apart : ∀i j,i≠j → Disjoint (A i) (A j))
    (detached : ∀i j,i≠j → ∀x∈A i,∀y∈A j,¬(Q.induce Iᶜ).Adj x y) :
    ∀i,(A i).ncard=1 ∨ (A i).ncard=D := by
  classical
  let C (i : J) : Set X := Subtype.val '' A i
  have cardC (i) : (C i).ncard=(A i).ncard := Set.ncard_image_of_injective _ Subtype.val_injective
  have dis (i j : J) (ne : i≠j) := Set.disjoint_image_of_injective Subtype.val_injective (apart i j ne)
  have cl (i : J) : Q.IsClique (C i) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ ne
    exact clique i hx hy (fun eq => ne (congrArg Subtype.val eq))
  have ext (i : J) (a : X) (ha : a∈C i) (b : X) (adj : Q.Adj a b) (out : b∉C i) : b∈I := by
    by_contra hb
    obtain ⟨x,hx,rfl⟩ := ha
    let y : ↥(Iᶜ : Set X) := ⟨b,hb⟩
    obtain ⟨j,hy⟩ := cover y
    have diff : i≠j := fun eq => out ⟨y,eq.symm ▸ hy,rfl⟩
    exact detached i j diff x hx y hy adj
  have cap (i : J) : (C i).ncard≤D := by
    apply outside_largest_clique_size Q I _ ind largest _ (cl i) D (fun x => (reg x).le)
    rintro _ ⟨x,_,rfl⟩
    exact x.property
  have pos (i : J) : 1≤(C i).ncard := cardC i ▸ (Set.ncard_pos (Set.toFinite _)).mpr (nonempty i)
  have sizes := tight_clique_family_sizes Q C I D same dis cl (fun _ x _ => reg x) pos cap ext
    (fun x _ => (reg x).le)
  exact fun i => cardC i ▸ sizes i

/-- If the nonempty zero region is detached from every pointed block, and
each pointed block is a clique, every block has size 1 or D. This includes
the original matching partition and requires the exceptional class empty. -/
theorem detached_mate_sizes (Q : SimpleGraph X) (I : Set X) (ind : Q.IsIndepSet I)
    (largest : ∀S : Set X,Q.IsIndepSet S → S.ncard≤I.ncard)
    (D : ℕ) (reg : ∀x,Nat.card (Q.neighborSet x)=D)
    (N : (Q.induce Iᶜ).Subgraph) (hm : N.IsMatching) (max : N.edgeSet.ncard=matchingEdges (Q.induce Iᶜ))
    (gap : N.vertsᶜ.ncard+1=I.ncard) (noEx : exceptionalMateRegion (Q.induce Iᶜ) N=∅)
    (nonZ : (zeroMateRegion (Q.induce Iᶜ) N).Nonempty)
    (clZ : (Q.induce Iᶜ).IsClique (zeroMateRegion (Q.induce Iᶜ) N))
    (clB : ∀w,w∉N.verts → (Q.induce Iᶜ).IsClique (mateBlock (Q.induce Iᶜ) N w))
    (noContact : ∀w,w∉N.verts → ∀a∈mateBlock (Q.induce Iᶜ) N w,∀b∈zeroMateRegion (Q.induce Iᶜ) N,
      ¬(Q.induce Iᶜ).Adj a b) :
    ∀w,w∉N.verts → (mateBlock (Q.induce Iᶜ) N w).ncard=1 ∨ (mateBlock (Q.induce Iᶜ) N w).ncard=D := by
  classical
  let H := Q.induce Iᶜ
  let U := ↥(N.vertsᶜ)
  let _ : Fintype U := Fintype.ofFinite U
  let A : Option U → Set ↥(Iᶜ : Set X)
    | none => zeroMateRegion H N
    | some w => mateBlock H N w.val
  have count : Nat.card (Option U)=I.ncard := by
    rw [Nat.card_eq_fintype_card,Fintype.card_option,←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
    exact gap
  have cover (v : ↥(Iᶜ : Set X)) : ∃i,v∈A i := by
    rcases mate_classes_cover H N hm v with ⟨w,hw,hv⟩|z|e
    · exact ⟨some ⟨w,hw⟩,hv⟩
    · exact ⟨none,z⟩
    · exact (noEx ▸ e : v∈(∅ : Set ↥(Iᶜ : Set X))).elim
  have pos : ∀i,(A i).Nonempty := by
    rintro (_|w)
    · exact nonZ
    · exact ⟨w.val,mateBlock_self H N w.val⟩
  have cl : ∀i,H.IsClique (A i) := by
    rintro (_|w)
    · exact clZ
    · exact clB w.val w.property
  have apart : ∀i j,i≠j → Disjoint (A i) (A j) := by
    rintro (_|w) (_|u) ne
    · exact (ne rfl).elim
    · exact (mate_block_disjoint_zero H N hm u.val u.property).symm
    · exact mate_block_disjoint_zero H N hm w.val w.property
    · exact different_mate_blocks_disjoint H N hm max w.val u.val w.property u.property
        (fun eq => ne (congrArg some (Subtype.ext eq)))
  have detached : ∀i j,i≠j → ∀a∈A i,∀b∈A j,¬H.Adj a b := by
    rintro (_|w) (_|u) ne a ha b hb edge
    · exact ne rfl
    · exact noContact u.val u.property b hb a ha edge.symm
    · exact noContact w.val w.property a ha b hb edge
    · exact clique_mate_blocks_separated H N hm max w.val u.val w.property u.property
        (fun eq => ne (congrArg some (Subtype.ext eq))) (clB _ w.property) (clB _ u.property) a ha b hb edge
  have sizes := original_detached_clique_sizes Q I ind largest D reg A count pos cl cover apart detached
  exact fun w hw => sizes (some ⟨w,hw⟩)

#print axioms detached_mate_sizes
end JSP452Audit.StarHost
