import OriginalExceptionalPartition
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- The unique nontrivial exceptional clique, on original labels, together
with the singleton parts and their distinguished heavy endpoint. -/
structure HeavyCliqueFrame (Q : SimpleGraph X) (I : Set X) (D : ℕ) where
  pivot : X
  singles : Set X
  cliquePart : Set X
  ai : pivot∉I
  sOut : singles⊆Iᶜ
  cOut : cliquePart⊆Iᶜ
  dis : Disjoint singles cliquePart
  as_ : pivot∉singles
  ac : pivot∉cliquePart
  cover : ∀v,v∈I ∨ v=pivot ∨ v∈singles ∨ v∈cliquePart
  singleEdges : ∀s∈singles,∀v,Q.Adj s v → v∈I ∨ v=pivot
  cliqueEdges : ∀c∈cliquePart,∀v,Q.Adj c v → v∉cliquePart → v∈I ∨ v=pivot
  clique : Q.IsClique cliquePart
  order : cliquePart.ncard=D-1
  count : singles.ncard+1=I.ncard
  two : ∃u∈singles,∃v∈singles,u≠v ∧ Q.Adj pivot u ∧ Q.Adj pivot v

theorem lift_exceptional_big_clique {J : Type*} [Fintype J] (Q : SimpleGraph X) (I : Set X)
    (D : ℕ) (a : ↥(Iᶜ : Set X)) (F : J→Set ↥(Iᶜ : Set X)) (count : Fintype.card J=I.ncard)
    (dis : ∀i j,i≠j → Disjoint (F i) (F j)) (off : ∀i,a∉F i)
    (cover : ∀v,v≠a → ∃i,v∈F i) (sep : ∀i j,i≠j → ∀v∈F i,∀w∈F j,¬(Q.induce Iᶜ).Adj v w)
    (q:J) (cl : (Q.induce Iᶜ).IsClique (F q)) (big : (F q).ncard=D-1)
    (others : ∀i,i≠q → (F i).ncard=1) (two : ∃u v,u≠v ∧ u∉F q ∧ v∉F q ∧ (Q.induce Iᶜ).Adj a u ∧ (Q.induce Iᶜ).Adj a v) :
    ∃s : HeavyCliqueFrame Q I D,s.pivot=a.val ∧ s.cliquePart=Subtype.val '' F q := by
  classical
  let K := {i:J | i≠q}
  let _ := Fintype.ofFinite K
  let S := ⋃j:K,F j.val
  let C := F q
  have apart : Disjoint S C := by
    apply Set.disjoint_left.mpr
    intro v mem h
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp mem
    exact Set.disjoint_left.mp (dis j.val q j.property) hj h
  have outside (A : Set ↥(Iᶜ : Set X)) : Subtype.val '' A⊆Iᶜ := by rintro _ ⟨v,_,rfl⟩;exact v.property
  have as_ : a∉S := by intro h; obtain ⟨j,hj⟩ := Set.mem_iUnion.mp h;exact off j.val hj
  have classify (v : ↥(Iᶜ : Set X)) (va:v≠a) : v∈S ∨ v∈C := by
    obtain ⟨j,hj⟩ := cover v va
    by_cases eq:j=q
    · exact Or.inr (show v∈F q from eq ▸ hj)
    · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨j,eq⟩,hj⟩)
  have cardS : S.ncard+1=I.ncard := by
    have sizes : S.ncard=Nat.card K := by
      rw [show S=⋃j:K,F j.val from rfl,Set.ncard_iUnion_of_finite (fun j => Set.toFinite (F j.val))
        (fun i j ne => dis _ _ (fun eq => ne (Subtype.ext eq))),finsum_eq_sum_of_fintype,Nat.card_eq_fintype_card]
      simp [fun i:K => others i.val i.property]
    rw [sizes,Nat.card_coe_set_eq,show K=({q}:Set J)ᶜ by ext; simp [K],Set.ncard_compl,Set.ncard_singleton,
      Nat.card_eq_fintype_card,←count]
    have pos := Fintype.card_pos_iff.mpr (show Nonempty J from ⟨q⟩)
    omega
  obtain ⟨u,v,uv,uc,vc,au,av⟩ := two
  have us : u∈S := (classify u au.ne.symm).resolve_right uc
  have vs : v∈S := (classify v av.ne.symm).resolve_right vc
  refine ⟨{
    pivot := a.val
    singles := Subtype.val '' S
    cliquePart := Subtype.val '' C
    ai := a.property
    sOut := outside _
    cOut := outside _
    dis := Set.disjoint_image_of_injective Subtype.val_injective apart
    as_ := ?_
    ac := ?_
    cover := ?_
    singleEdges := ?_
    cliqueEdges := ?_
    clique := ?_
    order := (Set.ncard_image_of_injective _ Subtype.val_injective).trans big
    count := (congrArg (fun n:ℕ => n+1) (Set.ncard_image_of_injective _ Subtype.val_injective)).trans cardS
    two := ⟨u.val,⟨u,us,rfl⟩,v.val,⟨v,vs,rfl⟩,fun eq => uv (Subtype.ext eq),au,av⟩
  },rfl,rfl⟩
  · rintro ⟨v,hv,h⟩;exact as_ ((Subtype.ext h : v=a) ▸ hv)
  · rintro ⟨v,hv,h⟩;exact off q ((Subtype.ext h : v=a) ▸ hv)
  · intro v
    by_cases vi:v∈I
    · exact Or.inl vi
    let w : ↥(Iᶜ : Set X) := ⟨v,vi⟩
    by_cases eq:w=a
    · exact Or.inr (Or.inl (congrArg Subtype.val eq))
    rcases classify w eq with hs|hc
    · exact Or.inr (Or.inr (Or.inl ⟨w,hs,rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨w,hc,rfl⟩))
  · rintro _ ⟨v,hv,rfl⟩ w edge
    by_cases wi:w∈I
    · exact Or.inl wi
    by_cases wa:w=a.val
    · exact Or.inr wa
    let z : ↥(Iᶜ : Set X) := ⟨w,wi⟩
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hv
    obtain ⟨k,hk⟩ := cover z (fun eq => wa (congrArg Subtype.val eq))
    by_cases eq:j.val=k
    · have same := (Set.ncard_le_one (Set.toFinite _)).mp (others j.val j.property).le v hj z (eq.symm ▸ hk)
      exact ((show Q.Adj v.val z.val from edge).ne (congrArg Subtype.val same)).elim
    · exact (sep j.val k eq v hj z hk edge).elim
  · rintro _ ⟨v,hv,rfl⟩ w edge away
    by_cases wi:w∈I
    · exact Or.inl wi
    by_cases wa:w=a.val
    · exact Or.inr wa
    let z : ↥(Iᶜ : Set X) := ⟨w,wi⟩
    obtain ⟨k,hk⟩ := cover z (fun eq => wa (congrArg Subtype.val eq))
    have diff : q≠k := fun eq => away ⟨z,(show z∈F q from eq.symm ▸ hk),rfl⟩
    exact (sep q k diff v hv z hk edge).elim
  · rintro _ ⟨v,hv,rfl⟩ _ ⟨w,hw,rfl⟩ ne
    exact cl hv hw (fun eq => ne (congrArg Subtype.val eq))

#print axioms lift_exceptional_big_clique
end JSP452Audit.StarHost
