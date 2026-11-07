import ForcedRootAtBadCut
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Preserve which root is the actual exit for this particular matching. -/
theorem single_exit_for_matching (Q : SimpleGraph X) (I : Set X) (ind : Q.IsIndepSet I)
    (s : OnePreferredPart Q I) (i : X) (hi:i∈I) (M : Q.Subgraph) (hm : M.IsMatching)
    (supp : M.verts={v|v≠i}) :
    ∃u∈I,u≠i ∧ ∃p∈s.preferred,M.Adj u p ∧
      ∀a∈s.preferred,∀b,M.Adj a b → b∉s.preferred → b=u := by
  classical
  let W := independentMateLabels Q I i M
  have usedNe {a b} (edge:M.Adj a b) : a≠i := by
    have h := M.edge_vert edge
    rwa [supp] at h
  have sub : s.singles⊆W := by
    intro v hv
    have active : v∈M.verts := by rw [supp];exact fun eq => s.sOut hv (eq.symm ▸ hi)
    obtain ⟨u,edge,_⟩ := hm active
    exact ⟨s.sOut hv,u,s.isolated v hv u (M.adj_sub edge),usedNe edge.symm,edge.symm⟩
  have wc : W.ncard+1=I.ncard := independentMateLabels_card Q I ind i hi M hm supp
  have cnt := s.count
  obtain ⟨p,pW,ps⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (show s.singles.ncard<W.ncard by omega)
  have pp : p∈s.preferred := (s.cover p).elim (fun h => (pW.1 h).elim)
    (fun h => h.resolve_left ps)
  obtain ⟨_,u,hu,ui,up⟩ := pW
  have exactW : insert p s.singles=W := by
    apply Set.eq_of_subset_of_ncard_le
    · exact Set.insert_subset (show p∈W from ⟨s.pOut pp,u,hu,ui,up⟩) sub
    · rw [Set.ncard_insert_of_notMem ps];omega
    · exact Set.toFinite W
  refine ⟨u,hu,ui,p,pp,up,?_⟩
  intro a ha b edge out
  have bi := s.external a ha b (M.adj_sub edge) out
  have aW : a∈W := ⟨s.pOut ha,b,bi,usedNe edge.symm,edge.symm⟩
  rw [←exactW] at aW
  rcases aW with same|hs
  · subst a;exact hm.eq_of_adj_left edge up.symm
  · exact (Set.disjoint_left.mp s.dis hs ha).elim

/-- The outside of the old matching is kept intact. Within the preferred part
and its exit root use the root-leaf edge and the even clique away from a. -/
theorem cut_triple_matching (Q : SimpleGraph X) (I : Set X) (s : OnePreferredPart Q I)
    (D : ℕ) (par : Even D) (six : 6≤D)
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

#print axioms single_exit_for_matching
#print axioms cut_triple_matching
end JSP452Audit.StarHost
