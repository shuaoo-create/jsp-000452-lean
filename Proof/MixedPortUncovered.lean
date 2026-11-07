import GoodPortParts
import PairFamily
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- If an internal matching on the full vertices leaves just one more hole than
there are low vertices, its uncovered original vertices form a clique. -/
theorem uncovered_clique_of_good_low (Q : SimpleGraph X) (D : ℕ)
    (cap : ∀ x, Nat.card (Q.neighborSet x) ≤ D) (crit : PerfectAfterEveryDeletion Q)
    (good : ∀ x ∈ portLow Q D, GoodPort Q x)
    (H : (Q.induce (portFull Q D)).Subgraph) (hm : H.IsMatching)
    (size : H.vertsᶜ.ncard = (portLow Q D).ncard + 1) :
    (Q.induce (portFull Q D)).IsClique H.vertsᶜ := by
  classical
  let F := portFull Q D
  let U := portLow Q D
  let _ := Fintype.ofFinite X
  have apart (x : X) (hi : x ∈ F) (lo : x ∈ U) : False := Nat.ne_of_lt lo hi
  let inc := SimpleGraph.Embedding.induce (G := Q) F
  let P := H.map inc.toHom
  have mP : P.IsMatching := hm.map inc.toHom inc.injective
  intro v hv z hz vz
  let avail : Set F := H.vertsᶜ \ {v}
  have card : avail.ncard = U.ncard := by
    have count := Set.ncard_sdiff_add_ncard_of_subset (Set.singleton_subset_iff.mpr hv)
    rw [Set.ncard_singleton,size] at count
    exact Nat.add_right_cancel count
  let _ := Fintype.ofFinite U
  let _ := Fintype.ofFinite avail
  let e : U ≃ avail := Fintype.equivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] using card.symm)
  let l : U ↪ X := Function.Embedding.subtype _
  let r : U ↪ X := (e.toEmbedding.trans (Function.Embedding.subtype _)).trans (Function.Embedding.subtype _)
  have edges (u : U) : Q.Adj (l u) (r u) :=
    (full_adj_good_low Q D cap crit good (e u).val.property u.property).symm
  let K := Padded.pairFamily Q l r edges
  have LR : Disjoint (Set.range l) (Set.range r) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨u,rfl⟩ ⟨w,eq⟩
    exact apart _ (show l u ∈ F from eq ▸ (e w).val.property) u.property
  have mK : K.IsMatching := Padded.pairFamily_isMatching Q l r edges LR
  have PK : Disjoint P.verts K.verts := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨x,hx,rfl⟩ (⟨u,eq⟩ | ⟨u,eq⟩)
    · have same : u.val = x.val := eq
      exact apart _ x.property (same ▸ u.property)
    · have same : (e u).val = x := Subtype.ext eq
      exact (e u).property.1 (same.symm ▸ hx)
  let N := P ⊔ K
  have matchN : N.IsMatching := Padded.matching_sup_of_disjoint_verts Q mP mK PK
  have support : N.verts = {x | x ≠ v.val} := by
    ext x
    constructor
    · intro h eq
      subst x
      rcases h with ⟨w,hw,eq⟩ | (⟨u,eq⟩ | ⟨u,eq⟩)
      · exact hv ((Subtype.ext eq : w = v) ▸ hw)
      · exact apart _ v.property (eq ▸ u.property)
      · exact (e u).property.2 (Set.mem_singleton_iff.mpr (Subtype.ext eq))
    · intro ne
      by_cases full : x ∈ F
      · let w : F := ⟨x,full⟩
        by_cases used : w ∈ H.verts
        · exact Or.inl ⟨w,used,rfl⟩
        · have neq : w ≠ v := fun h => ne (congrArg Subtype.val h)
          let hole : avail := ⟨w,used,fun h => neq (Set.mem_singleton_iff.mp h)⟩
          exact Or.inr (Or.inr ⟨e.symm hole,congrArg (fun w : avail => w.val.val) (e.apply_symm_apply hole)⟩)
      · have low : x ∈ U := lt_of_le_of_ne (cap x) full
        exact Or.inr (Or.inl ⟨⟨x,low⟩,rfl⟩)
  let hole : avail := ⟨z,hz,fun h => vz (Set.mem_singleton_iff.mp h).symm⟩
  let u := e.symm hole
  have right : r u = z.val := congrArg (fun h : avail => h.val.val) (e.apply_symm_apply hole)
  have matched : N.Adj (l u) z.val :=
    Or.inr (Or.inl ⟨u,rfl,right⟩)
  have diff : v.val ≠ l u := fun he => apart _ v.property (he.symm ▸ u.property)
  exact good (l u) u.property v.val diff N matchN support z.val matched

#print axioms uncovered_clique_of_good_low
end JSP452Audit.StarHost
