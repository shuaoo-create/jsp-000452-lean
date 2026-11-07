import ShortCompleteStageInOddSixRegular
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_six_selected_short_stage (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (T:Finset F.G.ConnectedComponent) (actual:∀c∈T,c∈oddRegularComponents F.G 6) :
    let U := componentVertices F.G T
    ∃A:Set U,CompleteDegreeStage (F.G.induce U) 6 A ∧ A.ncard+T.card≤matchingEdges (F.G.induce U) := by
  classical
  intro U
  have localStage (c:↥T) : ∃J:Set c.val.supp,CompleteDegreeStage c.val.toSimpleGraph 6 J ∧
      J.ncard+1≤matchingEdges c.val.toSimpleGraph := by
    obtain ⟨_,order,_,edges⟩ := strict_six_true_component_capacity F paid six c.val (actual c.val c.property)
    have reg (v:c.val.supp) := (component_degree_eq F.G c.val v).trans ((actual c.val c.property).2 v.val v.property)
    exact short_stage_odd_six_regular _ _ reg order edges
  choose J stage small using localStage
  let embed (c:↥T) : c.val.supp ↪ U := {
    toFun := fun x => ⟨x.val,by change F.G.connectedComponentMk x.val∈T;rw [show F.G.connectedComponentMk x.val=c.val from x.property];exact c.property⟩
    inj' := fun _ _ eq => Subtype.ext (congrArg (fun x:U => x.val) eq) }
  let part (c:↥T) := embed c '' J c
  let A := ⋃c:↥T,part c
  have label {c:↥T} {x:U} (mem:x∈part c) : F.G.connectedComponentMk x.val=c.val := by
    obtain ⟨v,_,rfl⟩ := mem;exact v.property
  have dis : Pairwise (Function.onFun Disjoint part) := fun c e ne => Set.disjoint_left.mpr
    (fun x hc he => ne (Subtype.ext ((label hc).symm.trans (label he))))
  have tally (c:↥T) : (part c).ncard=(J c).ncard := Set.ncard_image_of_injective _ (embed c).injective
  have card := Set.ncard_iUnion_of_finite (fun c => (part c).toFinite) dis
  rw [finsum_eq_sum_of_fintype] at card
  simp only [tally] at card
  change A.ncard=∑c:↥T,(J c).ncard at card
  have cmp := Finset.sum_le_sum (s:=(Finset.univ:Finset ↥T)) (fun c _ => small c)
  rw [Finset.sum_add_distrib,Finset.sum_const] at cmp
  simp only [Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,Nat.cast_id,mul_one,←card] at cmp
  have sum := Finset.sum_coe_sort T (fun c => matchingEdges c.toSimpleGraph)
  rw [sum] at cmp
  have rank := (component_union_accounts F.G T).2.1
  have closed := component_vertices_closed F.G T
  have reg (v:U) : Nat.card ((F.G.induce U).neighborSet v)=6 :=
    (closed_set_degree_eq F.G U closed v).trans ((actual (F.G.connectedComponentMk v.val) v.property).2 v.val rfl)
  refine ⟨A,⟨?_,fun v _ => reg v,?_⟩,cmp.trans_eq rank.symm⟩
  · intro x hx y hy ne edge
    obtain ⟨c,xc⟩ := Set.mem_iUnion.mp hx
    obtain ⟨e,ye⟩ := Set.mem_iUnion.mp hy
    have same : c=e := Subtype.ext ((label xc).symm.trans ((ConnectedComponent.sound (show F.G.Adj x.val y.val from edge).reachable).trans (label ye)))
    subst e
    obtain ⟨v,hv,rfl⟩ := xc
    obtain ⟨w,hw,rfl⟩ := ye
    exact (stage c).1 hv hw (fun eq => ne (congrArg (embed c) eq)) edge
  · intro v _
    let c:↥T := ⟨F.G.connectedComponentMk v.val,v.property⟩
    let x:c.val.supp := ⟨v.val,rfl⟩
    have deg := (component_degree_eq F.G c.val x).trans ((actual c.val c.property).2 v.val rfl)
    rcases (stage c).2.2 x deg with mem|⟨w,hw,edge⟩
    · exact Or.inl (Set.mem_iUnion.mpr ⟨c,x,mem,Subtype.ext rfl⟩)
    · exact Or.inr ⟨embed c w,Set.mem_iUnion.mpr ⟨c,w,hw,rfl⟩,edge⟩

theorem strict_six_short_shadow (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (T:Finset F.G.ConnectedComponent) (actual:∀c∈T,c∈oddRegularComponents F.G 6)
    (B:Set ↥((componentVertices F.G T)ᶜ:Set F.X)) (stage:CompleteDegreeStage (F.G.induce (componentVertices F.G T)ᶜ) 6 B) :
    widthAt F.n F.m F.r 6+T.card≤matchingEdges (F.G.induce (componentVertices F.G T))+B.ncard+
      (2*highestWidth F.n F.m F.r+10)/3 := by
  obtain ⟨A,full,short⟩ := strict_six_selected_short_stage F paid six T actual
  have bound := strict_six_shadow_on_actual_exterior F paid six _ (component_vertices_closed F.G T) A B full stage
  omega

#print axioms strict_six_selected_short_stage
#print axioms strict_six_short_shadow
end JSP452Audit.StarHost
