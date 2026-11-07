import FourDetachedPrices
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- The original labels of the two triangles and isolated residual vertices. -/
structure TwinTriangleParts (Q : SimpleGraph X) (I : Set X) where
  P : Set X
  C : Set X
  S : Set X
  pSize : P.ncard=3
  cSize : C.ncard=3
  pClique : Q.IsClique P
  cClique : Q.IsClique C
  pc : Disjoint P C
  sp : Disjoint S P
  sc : Disjoint S C
  pOut : P⊆Iᶜ
  cOut : C⊆Iᶜ
  sOut : S⊆Iᶜ
  count : S.ncard+3=I.ncard
  cover : ∀v,v∈I ∨ v∈S ∨ v∈P ∨ v∈C
  isolated : ∀v∈S,∀u,Q.Adj v u → u∈I
  pExt : ∀v∈P,∀u,Q.Adj v u → u∉P → u∈I
  cExt : ∀v∈C,∀u,Q.Adj v u → u∉C → u∈I

theorem original_twin_triangles (Q : SimpleGraph X) (I : Set X)
    (s : DetachedMatePair (Q.induce Iᶜ)) (count : s.singles.ncard+3=I.ncard)
    (p3 : (Subtype.val '' s.preferred).ncard=3) (c3 : (Subtype.val '' s.companion).ncard=3)
    (pcl : Q.IsClique (Subtype.val '' s.preferred)) :
    ∃h : TwinTriangleParts Q I,h.P=Subtype.val '' s.preferred ∧ h.C=Subtype.val '' s.companion := by
  classical
  let P := Subtype.val '' s.preferred
  let C := Subtype.val '' s.companion
  let S := Subtype.val '' s.singles
  have outside (A : Set ↥(Iᶜ : Set X)) : Subtype.val '' A⊆Iᶜ := by
    rintro _ ⟨v,_,rfl⟩;exact v.property
  have singles (a:X) (ha:a∈S) (v:X) (edge:Q.Adj a v) : v∈I := by
    by_contra vi
    obtain ⟨t,ht,rfl⟩ := ha
    exact s.isolated t ht ⟨v,vi⟩ edge
  have pExt (a:X) (ha:a∈P) (v:X) (edge:Q.Adj a v) (out:v∉P) : v∈I := by
    by_contra vi
    obtain ⟨t,ht,rfl⟩ := ha
    let w : ↥(Iᶜ : Set X) := ⟨v,vi⟩
    rcases s.cover w with hs|hc|hp
    · exact s.isolated w hs t edge.symm
    · exact s.apart_edges t ht w hc edge
    · exact out ⟨w,hp,rfl⟩
  have cExt (a:X) (ha:a∈C) (v:X) (edge:Q.Adj a v) (out:v∉C) : v∈I := by
    by_contra vi
    obtain ⟨t,ht,rfl⟩ := ha
    let w : ↥(Iᶜ : Set X) := ⟨v,vi⟩
    rcases s.cover w with hs|hc|hp
    · exact s.isolated w hs t edge.symm
    · exact out ⟨w,hc,rfl⟩
    · exact s.apart_edges w hp t ht edge.symm
  have liftCount : S.ncard+3=I.ncard := by
    rw [show S.ncard=s.singles.ncard from Set.ncard_image_of_injective _ Subtype.val_injective,count]
  have cl : Q.IsClique C := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ ne
    exact s.companion_clique ha hb (fun e => ne (congrArg Subtype.val e))
  have cover (v : X) : v∈I ∨ v∈S ∨ v∈P ∨ v∈C := by
    by_cases inside : v∈I
    · exact Or.inl inside
    let u : ↥(Iᶜ : Set X) := ⟨v,inside⟩
    rcases s.cover u with hs|hc|hp
    · exact Or.inr (Or.inl ⟨u,hs,rfl⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨u,hc,rfl⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨u,hp,rfl⟩))
  exact ⟨⟨P,C,S,p3,c3,pcl,cl,Set.disjoint_image_of_injective Subtype.val_injective s.apart,
    Set.disjoint_image_of_injective Subtype.val_injective s.sp,
    Set.disjoint_image_of_injective Subtype.val_injective s.sc,
    outside _,outside _,outside _,liftCount,cover,singles,pExt,cExt⟩,rfl,rfl⟩

theorem twin_triangle_two_root_neighbors (Q : SimpleGraph X) (I A : Set X) (size : A.ncard=3)
    (cl : Q.IsClique A) (outside : A⊆Iᶜ)
    (ext : ∀v∈A,∀w,Q.Adj v w → w∉A → w∈I) (reg : ∀v,Nat.card (Q.neighborSet v)=4)
    (v : X) (hv : v∈A) : (Q.neighborSet v∩I).ncard=2 := by
  let N := Q.neighborSet v
  have inside : N∩A=A\{v} := by
    ext w
    refine ⟨fun h => ⟨h.2,fun eq => (show Q.Adj v w from h.1).ne (Set.mem_singleton_iff.mp eq).symm⟩,?_⟩
    intro h
    exact ⟨cl hv h.1 (fun eq => h.2 (Set.mem_singleton_iff.mpr eq.symm)),h.1⟩
  have nb : N=(N∩I)∪(N∩A) := by
    ext w
    constructor
    · intro h
      by_cases ha : w∈A
      · exact Or.inr ⟨h,ha⟩
      · exact Or.inl ⟨h,ext v hv w h ha⟩
    · exact fun h => h.elim And.left And.left
  have dis : Disjoint (N∩I) (N∩A) := Set.disjoint_left.mpr (fun _ hi ha => outside ha.2 hi.2)
  have total : N.ncard=4 := (Nat.card_coe_set_eq _).symm.trans (reg v)
  have rm := Set.ncard_sdiff_singleton_add_one hv
  calc
    (Q.neighborSet v∩I).ncard = (N∩I).ncard := rfl
    _ = 2 := by rw [nb,Set.ncard_union_eq dis,inside] at total;omega

#print axioms original_twin_triangles
#print axioms twin_triangle_two_root_neighbors
end JSP452Audit.StarHost
