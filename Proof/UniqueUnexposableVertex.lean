import RealCutSides
import CliquePairs
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private theorem match_even_clique_set (G : SimpleGraph X) (C : Set X)
    (cl : G.IsClique C) (even : Even C.ncard) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.verts = C := by
  let e : C ↪ X := ⟨Subtype.val, Subtype.val_injective⟩
  have ce : Even (Nat.card C) := by simpa only [Nat.card_coe_set_eq] using even
  obtain ⟨M,hm,supp⟩ := JSP452Audit.Padded.existsMatchingOnEvenClique G e
    (fun {i j} ne => cl i.property j.property (fun eq => ne (Subtype.ext eq))) ce
  refine ⟨M,hm,supp.trans ?_⟩
  ext z
  constructor
  · rintro ⟨v,rfl⟩; exact v.property
  · intro hz; exact ⟨⟨z,hz⟩,rfl⟩

private theorem even_sides_expose (G : SimpleGraph X) (x : X) (A B : Set X)
    (apart : Disjoint A B) (cover : A ∪ B = {v | v ≠ x}) (ca : G.IsClique A)
    (cb : G.IsClique B) (ea : Even A.ncard) (eb : Even B.ncard) : ExposablePoint G x := by
  obtain ⟨L,ml,sl⟩ := match_even_clique_set G A ca ea
  obtain ⟨R,mr,sr⟩ := match_even_clique_set G B cb eb
  have d : Disjoint L.verts R.verts := by rwa [sl,sr]
  apply exposable_of_single_hole G x (L ⊔ R)
    (JSP452Audit.Padded.matching_sup_of_disjoint_verts G ml mr d)
  rw [Subgraph.verts_sup,sl,sr]; exact cover

private theorem odd_erase_even {S : Set X} {a : X}
    (odd : Odd S.ncard) (ha : a ∈ S) : Even (S \ {a}).ncard := by
  have count := Set.ncard_sdiff_singleton_add_one ha
  have par := Nat.odd_iff.mp odd
  rw [Nat.even_iff]; omega

private theorem odd_sides_expose_left (G : SimpleGraph X)
    (x y b : X) (A B : Set X) (apart : Disjoint A B)
    (cover : A ∪ B = {v | v ≠ x}) (ca : G.IsClique A) (cb : G.IsClique B)
    (oa : Odd A.ncard) (ob : Odd B.ncard) (hy : y ∈ A) (hb : b ∈ B)
    (join : G.Adj x b) : ExposablePoint G y := by
  classical
  have split (v : X) : (v ∈ A ∨ v ∈ B) ↔ v ≠ x := by
    change v ∈ A ∪ B ↔ v ∈ {z | z ≠ x}; rw [cover]
  have xa : x ∉ A := fun h => (split x).mp (Or.inl h) rfl
  have xb : x ∉ B := fun h => (split x).mp (Or.inr h) rfl
  have yx : y ≠ x := (split y).mp (Or.inl hy)
  have ba : b ∉ A := fun h => Set.disjoint_left.mp apart h hb
  have by_ : b ≠ y := by rintro rfl; exact ba hy
  obtain ⟨L,ml,sl⟩ := match_even_clique_set G (A \ {y})
    (ca.subset (fun _ h => h.1)) (odd_erase_even oa hy)
  obtain ⟨R,mr,sr⟩ := match_even_clique_set G (B \ {b})
    (cb.subset (fun _ h => h.1)) (odd_erase_even ob hb)
  have lr : Disjoint L.verts R.verts := by
    rw [sl,sr]; exact apart.mono (fun _ h => h.1) (fun _ h => h.1)
  let E := G.subgraphOfAdj join
  have se : E.verts = {x,b} := rfl
  have away : Disjoint (L ⊔ R).verts E.verts := by
    rw [Subgraph.verts_sup,sl,sr,se]
    apply Set.disjoint_left.mpr
    intro v h edge
    rcases (Set.mem_insert_iff.mp edge) with vx|vb
    · subst v; exact h.elim (fun ha => xa ha.1) (fun hb' => xb hb'.1)
    · have eq := Set.mem_singleton_iff.mp vb
      subst v; exact h.elim (fun ha => ba ha.1) (fun hb' => hb'.2 (by simp))
  have mlr := JSP452Audit.Padded.matching_sup_of_disjoint_verts G ml mr lr
  have m := JSP452Audit.Padded.matching_sup_of_disjoint_verts G mlr
    (Subgraph.IsMatching.subgraphOfAdj join) away
  apply exposable_of_single_hole G y ((L ⊔ R) ⊔ E) m
  rw [Subgraph.verts_sup,Subgraph.verts_sup,sl,sr,se]
  ext v
  simp only [Set.mem_union,Set.mem_sdiff,Set.mem_singleton_iff,Set.mem_insert_iff,Set.mem_setOf_eq]
  constructor
  · rintro ((ha|hv)|vx|vb)
    · exact ha.2
    · intro vy; exact Set.disjoint_left.mp apart hy (vy ▸ hv.1)
    · intro vy; exact yx (vy.symm.trans vx)
    · intro vy; exact by_ (vb.symm.trans vy)
  · intro vy
    by_cases vx : v = x
    · exact Or.inr (Or.inl vx)
    by_cases vb : v = b
    · exact Or.inr (Or.inr vb)
    rcases (split v).mpr vx with ha|hv
    · exact Or.inl (Or.inl ⟨ha,vy⟩)
    · exact Or.inl (Or.inr ⟨hv,vb⟩)

/-- In a connected odd graph with independence number at most two, at most
one vertex cannot occur as the unique uncovered vertex of a matching. -/
theorem every_other_vertex_exposable (G : SimpleGraph X) (conn : G.Preconnected)
    (odd : Odd (Nat.card X)) (small : NoIndependentTriple G) (x : X)
    (bad : ¬ ExposablePoint G x) : ∀ y, y ≠ x → ExposablePoint G y := by
  have del : {v : X | v ≠ x} = ({x} : Set X)ᶜ := by ext; simp
  have order : {v : X | v ≠ x}.ncard + 1 = Nat.card X := by
    rw [del,Set.ncard_compl,Set.ncard_singleton]
    have pos : 0 < Nat.card X := @Nat.card_pos X ⟨x⟩ _
    omega
  have eo : Even {v : X | v ≠ x}.ncard := by
    have h := Nat.odd_iff.mp odd
    rw [Nat.even_iff]; omega
  have cut : ¬ (G.induce {v | v ≠ x}).Preconnected := by
    intro c
    apply bad
    exact perfect_of_preconnected_even_no_independent_triple _ c
      (by simpa only [Nat.card_coe_set_eq] using eo) (small.induce _)
  obtain ⟨A,B,_,_,dis,cover,ca,cb,_,⟨a,ha,xa⟩,⟨b,hb,xb⟩⟩ :=
    split_cut_into_two_cliques G conn small x cut
  have sizes : A.ncard + B.ncard = {v : X | v ≠ x}.ncard := by
    rw [←Set.ncard_union_eq dis,cover]
  have parity := Nat.even_iff.mp eo
  have notEven : ¬Even A.ncard := by
    intro evenA
    have pa := Nat.even_iff.mp evenA
    exact bad (even_sides_expose G x A B dis cover ca cb evenA (by rw [Nat.even_iff]; omega))
  have oa : Odd A.ncard := by
    rw [Nat.even_iff] at notEven
    rw [Nat.odd_iff]; omega
  have pa := Nat.odd_iff.mp oa
  have ob : Odd B.ncard := by rw [Nat.odd_iff]; omega
  intro y yx
  have mem : y ∈ A ∪ B := by rw [cover];exact yx
  rcases mem with hy | hy
  · exact odd_sides_expose_left G x y b A B dis cover ca cb oa ob hy hb xb
  · exact odd_sides_expose_left G x y a B A dis.symm (by rw [Set.union_comm,cover])
      cb ca ob oa hy ha xa

#print axioms every_other_vertex_exposable
end JSP452Audit.StarHost
