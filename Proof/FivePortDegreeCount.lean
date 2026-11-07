import FiveExposurePortGraph
namespace JSP452Audit.StarHost.FiveExposurePorts
open SimpleGraph
variable {X : Type*} [Finite X] {G : SimpleGraph X} (s : FiveExposurePorts G)
variable {Z : Type*} [Finite Z]

def project (x:X) : X⊕(s.U⊕Z) → X := Sum.elim id (Sum.elim Subtype.val (fun _ => x))

noncomputable def liftNeighbor (x y:X) : X⊕(s.U⊕Z) := by
  classical
  exact if hy : y∈s.U then (if s.target ⟨y,hy⟩=x then .inr (.inl ⟨y,hy⟩) else .inl y) else .inl y

theorem project_lift (x y:X) : s.project x (s.liftNeighbor (Z:=Z) x y)=y := by
  classical
  by_cases hy:y∈s.U
  · by_cases hit:s.target ⟨y,hy⟩=x <;> simp [liftNeighbor,project,hy,hit]
  · simp [liftNeighbor,project,hy]

theorem lift_injective (x:X) : Function.Injective (s.liftNeighbor (Z:=Z) x) := by
  intro y w eq
  simpa only [project_lift] using congrArg (s.project x) eq

private theorem old_image (J : SimpleGraph (s.U⊕Z)) (x:X) (v:X⊕(s.U⊕Z))
    (edge : (s.auxiliary J).Adj (.inl x) v) :
    G.Adj x (s.project x v) ∧ ¬s.M.Adj x (s.project x v) ∧
    (∀u:s.U,x=u.val → s.project x v≠s.target u) ∧
    s.liftNeighbor x (s.project x v)=v := by
  classical
  cases v with
  | inl y =>
    change s.kept x y at edge
    have unpicked := edge.2.2
    change G.Adj x y ∧ ¬s.M.Adj x y ∧ (∀u:s.U,x=u.val → y≠s.target u) ∧ _
    refine ⟨edge.1,edge.2.1,fun u hx hy => unpicked ⟨u,Set.mem_univ _,Or.inl ⟨hx.symm,hy.symm⟩⟩,?_⟩
    by_cases hy:y∈s.U
    · have off : s.target ⟨y,hy⟩≠x := fun hit => unpicked ⟨⟨y,hy⟩,Set.mem_univ _,Or.inr ⟨rfl,hit⟩⟩
      simp [project,liftNeighbor,hy,off]
    · simp [project,liftNeighbor,hy]
  | inr other =>
    cases other with
    | inl u =>
      change s.target u=x at edge
      subst x
      exact ⟨(s.link u).symm,fun e => s.missed u (s.M.edge_vert e.symm),
        fun w eq => (s.off u (eq.symm ▸ w.property)).elim,by simp [project,liftNeighbor,u.property]⟩
    | inr z => exact (show False from edge).elim

theorem old_port_degree_cap (J : SimpleGraph (s.U⊕Z)) (cap : ∀v,Nat.card (G.neighborSet v)≤5)
    (x:X) : Nat.card ((s.auxiliary J).neighborSet (.inl x))≤4 := by
  classical
  let N := (s.auxiliary J).neighborSet (.inl x)
  let f (v:N) := s.project x v.val
  have info (v:N) := s.old_image J x v.val v.property
  have inj : Function.Injective f := by
    intro v w eq
    exact Subtype.ext (((info v).2.2.2).symm.trans ((congrArg (s.liftNeighbor (Z:=Z) x) eq).trans (info w).2.2.2))
  have sub : Set.range f⊆G.neighborSet x := by rintro _ ⟨v,rfl⟩;exact (info v).1
  have size : (Set.range f).ncard=Nat.card N := Set.ncard_range_of_injective inj
  have total : (G.neighborSet x).ncard≤5 := (Nat.card_coe_set_eq _).symm.le.trans (cap x)
  have lower := Set.ncard_le_ncard sub
  change Nat.card N≤4
  by_contra! big
  have same : Set.range f=G.neighborSet x := Set.eq_of_subset_of_ncard_le sub (by omega)
  have five : Nat.card (G.neighborSet x)=5 := by rw [Nat.card_coe_set_eq];omega
  by_cases hx:x∈s.U
  · let u : s.U := ⟨x,hx⟩
    have mem : s.target u∈Set.range f := same.symm ▸ (s.link u)
    obtain ⟨v,eq⟩ := mem
    exact (info v).2.2.1 u rfl eq
  have matched : x∈s.M.verts := by
    by_contra away
    exact hx (by rw [s.exposed];exact ⟨away,five⟩)
  obtain ⟨w,edge,_⟩ := s.matching matched
  have mem : w∈Set.range f := same.symm ▸ (s.M.adj_sub edge)
  obtain ⟨v,eq⟩ := mem
  exact (info v).2.1 (show s.M.Adj x (f v) by rw [eq];exact edge)

theorem port_degree (J : SimpleGraph (s.U⊕Z)) (u:s.U) :
    Nat.card ((s.auxiliary J).neighborSet (.inr (.inl u)))=
      Nat.card (J.neighborSet (.inl u))+1 := by
  let Y := s.U⊕Z
  let inj : Y ↪ X⊕Y := Function.Embedding.inr
  have eq : (s.auxiliary J).neighborSet (.inr (.inl u)) =
      insert (.inl (s.target u)) (inj '' (J.neighborSet (.inl u))) := by
    ext v
    cases v with
    | inl x => simp [auxiliary,portAt,inj,SimpleGraph.mem_neighborSet,eq_comm]
    | inr y => simp [auxiliary,inj,SimpleGraph.mem_neighborSet]
  have out : (.inl (s.target u) : X⊕Y)∉inj '' (J.neighborSet (.inl u)) := by rintro ⟨y,_,e⟩;cases e
  rw [Nat.card_coe_set_eq,eq,Set.ncard_insert_of_notMem out,Set.ncard_image_of_injective _ inj.injective,
    Nat.card_coe_set_eq]

theorem extra_degree (J : SimpleGraph (s.U⊕Z)) (z:Z) :
    Nat.card ((s.auxiliary J).neighborSet (.inr (.inr z)))=Nat.card (J.neighborSet (.inr z)) := by
  let Y := s.U⊕Z
  let inj : Y ↪ X⊕Y := Function.Embedding.inr
  have eq : (s.auxiliary J).neighborSet (.inr (.inr z)) = inj '' (J.neighborSet (.inr z)) := by
    ext v
    cases v with
    | inl x => simp [auxiliary,portAt,inj,SimpleGraph.mem_neighborSet]
    | inr y => simp [auxiliary,inj,SimpleGraph.mem_neighborSet]
  rw [Nat.card_coe_set_eq,eq,Set.ncard_image_of_injective _ inj.injective,Nat.card_coe_set_eq]

#print axioms old_port_degree_cap
#print axioms port_degree
#print axioms extra_degree
end JSP452Audit.StarHost.FiveExposurePorts
