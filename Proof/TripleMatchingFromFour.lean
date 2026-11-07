import SingleCutTripleMatching
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- The outside of the old matching is kept intact. Within the preferred part
and its exit root use the root-leaf edge and the even clique away from a. -/
theorem cut_triple_matching_from_four (Q : SimpleGraph X) (I : Set X) (s : OnePreferredPart Q I)
    (D : ℕ) (par : Even D) (four : 4≤D)
    (x : s.preferred) (shape : BadSingleSplit Q s.preferred x.val D)
    (M : Q.Subgraph) (hm : M.IsMatching) (i r : X) (hi:i∈I) (hr:r∈I) (ir:i≠r)
    (a : X) (ha:a∈shape.side) (rb : Q.Adj r shape.leaf)
    (supp : M.verts={v|v≠i}) (p:X) (hp:p∈s.preferred) (rp:M.Adj r p)
    (only : ∀a∈s.preferred,∀b,M.Adj a b → b∉s.preferred → b=r) :
    ∃J : Q.Subgraph,J.IsMatching ∧ J.vertsᶜ={i,x.val,a} := by
  classical
  let P := s.preferred
  let A := shape.side
  let b := shape.leaf
  change a∈A at ha
  have bf : b∉A := shape.distinct
  let T := M.verts\(P∪{r})
  have sub : A⊆P\{x.val} := shape.parts ▸ Set.subset_union_left
  have bP : b∈P := (shape.parts ▸ (show b∈A∪{b} from Or.inr (by simp)) : b∈P\{x.val}).1
  have iP : i∉P := fun h => s.pOut h hi
  have rP : r∉P := fun h => s.pOut h hr
  have outer : (M.induce T).IsMatching := by
    intro v hv
    obtain ⟨w,edge,uniq⟩ := hm hv.1
    have outside : w∉P := by
      intro h
      have same := only w h v edge.symm (fun h => hv.2 (Or.inl h))
      exact hv.2 (Or.inr (Set.mem_singleton_iff.mpr same))
    have wr : w≠r := by
      intro eq
      have vw : M.Adj r v := eq ▸ edge.symm
      exact hv.2 (Or.inl ((hm.eq_of_adj_left vw rp).symm ▸ hp))
    have wt : w∈T := ⟨M.edge_vert edge.symm,fun h => h.elim outside (fun he => wr (Set.mem_singleton_iff.mp he))⟩
    exact ⟨w,⟨hv,wt,edge⟩,fun u h => uniq u h.2.2⟩
  let C := A\{a}
  have evenC : Even C.ncard := by
    have count := Set.ncard_sdiff_singleton_add_one ha
    have size : A.ncard=D-1 := shape.order
    have evenD := Nat.even_iff.mp par
    rw [Nat.even_iff];change (A\{a}).ncard%2=0;omega
  let e : C ↪ X := ⟨Subtype.val,Subtype.val_injective⟩
  obtain ⟨L,lm,origin⟩ := JSP452Audit.Padded.existsMatchingOnEvenClique Q e
    (fun {v w} ne => shape.clique v.property.1 w.property.1 (fun eq => ne (Subtype.ext eq)))
    (by rwa [Nat.card_coe_set_eq])
  have ls : L.verts=C := origin.trans (by ext v;exact ⟨fun ⟨w,eq⟩ => eq ▸ w.property,fun hv => ⟨⟨v,hv⟩,rfl⟩⟩)
  let E := Q.subgraphOfAdj rb
  have es : E.verts={r,b} := rfl
  have le : Disjoint L.verts E.verts := by
    rw [ls,es]
    apply Set.disjoint_left.mpr
    rintro v hv (eq|eq)
    · exact rP (eq ▸ (sub hv.1).1)
    · exact bf ((Set.mem_singleton_iff.mp eq) ▸ hv.1)
  have inner := JSP452Audit.Padded.matching_sup_of_disjoint_verts Q lm (Subgraph.IsMatching.subgraphOfAdj rb) le
  have dis : Disjoint (M.induce T).verts (L⊔E).verts := by
    rw [Subgraph.verts_sup,ls,es]
    apply Set.disjoint_left.mpr
    rintro v vt (lc|vr|vb)
    · exact vt.2 (Or.inl (sub lc.1).1)
    · exact vt.2 (Or.inr (Set.mem_singleton_iff.mpr vr))
    · exact vt.2 (Or.inl ((Set.mem_singleton_iff.mp vb).symm ▸ bP))
  let J := M.induce T ⊔ (L⊔E)
  have jm := JSP452Audit.Padded.matching_sup_of_disjoint_verts Q outer inner dis
  refine ⟨J,jm,?_⟩
  change (T∪(L.verts∪E.verts))ᶜ={i,x.val,a}
  rw [ls,es]
  have form : P=insert x.val (insert b A) := by
    ext v
    by_cases eq:v=x.val
    · subst v;simp
    · have iff := Set.ext_iff.mp shape.parts v
      simp [eq] at iff ⊢
      tauto
  have xa : x.val≠a := fun eq => shape.off (eq.symm ▸ ha)
  have ib : i≠b := fun eq => iP (eq.symm ▸ bP)
  have ix : i≠x.val := fun eq => iP (eq.symm ▸ x.property)
  have ia : i≠a := fun eq => iP (eq.symm ▸ (sub ha).1)
  have rx : r≠x.val := fun eq => rP (eq.symm ▸ x.property)
  have ra : r≠a := fun eq => rP (eq.symm ▸ (sub ha).1)
  have ab : a≠b := fun eq => bf (eq ▸ ha)
  have iA : i∉A := fun h => iP (sub h).1
  have xA : x.val∉A := shape.off
  have bx : b≠x.val := shape.leaf_off
  change (((M.verts\(P∪{r}))∪((A\{a})∪{r,b})))ᶜ={i,x.val,a}
  rw [supp,form]
  ext v
  simp only [Set.mem_compl_iff,Set.mem_union,Set.mem_sdiff,Set.mem_singleton_iff,
    Set.mem_insert_iff,Set.mem_ofPred_eq]
  by_cases vi:v=i
  · subst v;simp [ib,ir,iA,ix,ia]
  by_cases vx:v=x.val
  · subst v;simp [Ne.symm ix,Ne.symm rx,Ne.symm bx,xA,xa]
  by_cases va:v=a
  · subst v;simp [Ne.symm ia,Ne.symm xa,Ne.symm ra,ab,ha]
  simp only [vi,vx,va,not_false_eq_true]
  tauto

#print axioms cut_triple_matching_from_four
end JSP452Audit.StarHost
