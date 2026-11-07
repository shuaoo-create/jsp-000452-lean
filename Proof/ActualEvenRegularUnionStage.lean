import EightStageActualSevenPrice
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem odd_regular_order_edge_count {X:Type*} [Finite X] (G:SimpleGraph X) (p:ℕ)
    (odd:Odd (Nat.card X)) (reg:∀x,Nat.card (G.neighborSet x)=2*p) :
    Nat.card X=2*(Nat.card X/2)+1 ∧ G.edgeSet.ncard=(2*p)*(Nat.card X/2)+p := by
  classical
  let _ := Fintype.ofFinite X
  obtain ⟨P,order⟩ := odd
  have half : Nat.card X/2=P := by omega
  have deg (x:X) : G.degree x=2*p := by rw [←G.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card];exact reg x
  have hand := G.sum_degrees_eq_twice_card_edges
  simp only [deg,Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul,Nat.cast_id] at hand
  have edges : G.edgeFinset.card=G.edgeSet.ncard := by rw [←Nat.card_coe_set_eq,Nat.card_eq_fintype_card,SimpleGraph.edgeFinset_card]
  rw [edges,order] at hand
  rw [half];refine ⟨order,?_⟩
  have product : (2*P+1)*(2*p)=2*((2*p)*P+p) := by ring
  omega

theorem short_stages_on_odd_regular_components {X:Type*} [Finite X] (G:SimpleGraph X)
    (p:ℕ) (many:2≤p) (T:Finset G.ConnectedComponent) (actual:∀c∈T,c∈oddRegularComponents G (2*p)) :
    let U := componentVertices G T
    ∃A:Set U,CompleteDegreeStage (G.induce U) (2*p) A ∧ A.ncard+T.card≤∑c∈T,Nat.card c.supp/2 := by
  classical
  intro U
  have localStage (c:↥T) : ∃J:Set c.val.supp,CompleteDegreeStage c.val.toSimpleGraph (2*p) J ∧
      J.ncard+1≤Nat.card c.val.supp/2 := by
    have reg (v:c.val.supp) := (component_degree_eq G c.val v).trans ((actual c.val c.property).2 v.val v.property)
    obtain ⟨order,edges⟩ := odd_regular_order_edge_count c.val.toSimpleGraph p (actual c.val c.property).1 reg
    exact short_stage_odd_even_regular _ p _ many reg order edges
  choose J stage small using localStage
  let embed (c:↥T) : c.val.supp ↪ U := {
    toFun := fun x => ⟨x.val,by change G.connectedComponentMk x.val∈T;rw [show G.connectedComponentMk x.val=c.val from x.property];exact c.property⟩
    inj' := fun _ _ eq => Subtype.ext (congrArg (fun x:U => x.val) eq) }
  let part (c:↥T) := embed c '' J c
  let A := ⋃c:↥T,part c
  have label {c:↥T} {x:U} (mem:x∈part c) : G.connectedComponentMk x.val=c.val := by
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
  have sum := Finset.sum_coe_sort T (fun c => Nat.card c.supp/2)
  rw [sum] at cmp
  have closed := component_vertices_closed G T
  have reg (v:U) : Nat.card ((G.induce U).neighborSet v)=2*p :=
    (closed_set_degree_eq G U closed v).trans ((actual (G.connectedComponentMk v.val) v.property).2 v.val rfl)
  refine ⟨A,⟨?_,fun v _ => reg v,?_⟩,cmp⟩
  · intro x hx y hy ne edge
    obtain ⟨c,xc⟩ := Set.mem_iUnion.mp hx
    obtain ⟨e,ye⟩ := Set.mem_iUnion.mp hy
    have same : c=e := Subtype.ext ((label xc).symm.trans ((ConnectedComponent.sound (show G.Adj x.val y.val from edge).reachable).trans (label ye)))
    subst e
    obtain ⟨v,hv,rfl⟩ := xc
    obtain ⟨w,hw,rfl⟩ := ye
    exact (stage c).1 hv hw (fun eq => ne (congrArg (embed c) eq)) edge
  · intro v _
    let c:↥T := ⟨G.connectedComponentMk v.val,v.property⟩
    let x:c.val.supp := ⟨v.val,rfl⟩
    have deg := (component_degree_eq G c.val x).trans ((actual c.val c.property).2 v.val rfl)
    rcases (stage c).2.2 x deg with mem|⟨w,hw,edge⟩
    · exact Or.inl (Set.mem_iUnion.mpr ⟨c,x,mem,Subtype.ext rfl⟩)
    · exact Or.inr ⟨embed c w,Set.mem_iUnion.mpr ⟨c,w,hw,rfl⟩,edge⟩

theorem strict_eight_exterior_stage_bound (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (T:Finset F.G.ConnectedComponent) (actual:∀c∈T,c∈oddRegularComponents F.G 8)
    (B:Set ↥((componentVertices F.G T)ᶜ:Set F.X)) (stage:CompleteDegreeStage (F.G.induce (componentVertices F.G T)ᶜ) 8 B) :
    widthAt F.n F.m F.r 8+T.card≤(∑c∈T,Nat.card c.supp/2)+B.ncard+(22+2*highestWidth F.n F.m F.r)/5 := by
  obtain ⟨A,inner,size⟩ := short_stages_on_odd_regular_components F.G 4 (by decide) T actual
  obtain ⟨both,card⟩ := join_closed_degree_stages F.G _ 8 (component_vertices_closed F.G T) A B inner stage
  obtain ⟨_,_,_,_,lower,upper⟩ := strict_eight_complete_stage F paid eight _ both
  omega

#print axioms odd_regular_order_edge_count
#print axioms short_stages_on_odd_regular_components
#print axioms strict_eight_exterior_stage_bound
end JSP452Audit.StarHost
