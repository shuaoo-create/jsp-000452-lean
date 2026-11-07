import ActiveBoundaryPrice
import OrdinaryCliquePrice
import BlockCutBoundary
namespace JSP452Audit.StarHost
open SimpleGraph

private theorem count_paid_parts {J : Type*} [Fintype J] (f : J→ℕ) (A : Finset J)
    (p:J) (hp:p∈A) (D : ℕ)
    (total : (∑j,f j)≤(Fintype.card J+1)*D)
    (active : ∀j∈A,j≠p → 2*D-2≤f j) (inactive : ∀j,j∉A → D≤f j) :
    f p+(A.card-1)*(2*D-2)≤D*(A.card+1) := by
  classical
  let U : Finset J := Finset.univ
  let L := U\A
  let B := A.erase p
  have bCard : B.card=A.card-1 := Finset.card_erase_of_mem hp
  have aSum := Finset.sum_le_sum (s:=B) (fun j hj =>
    active j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1)
  have lSum := Finset.sum_le_sum (s:=L) (fun j hj => inactive j (Finset.mem_sdiff.mp hj).2)
  simp only [Finset.sum_const,smul_eq_mul,bCard] at aSum lSum
  have aPlus := Finset.sum_erase_add A f hp
  have split := Finset.sum_sdiff (f:=f) (Finset.subset_univ A)
  change (∑j∈B,f j)+f p=∑j∈A,f j at aPlus
  change (∑j∈L,f j)+(∑j∈A,f j)=∑j,f j at split
  have nL : L.card=Fintype.card J-A.card := by simp [L,U,Finset.card_sdiff]
  have nA := Finset.card_le_card (Finset.subset_univ A)
  simp only [Finset.card_univ] at nA
  have eq : Fintype.card J+1=L.card+(A.card+1) := by omega
  rw [eq,Nat.add_mul,Nat.mul_comm (A.card+1) D] at total
  omega

private theorem preferred_floor {X : Type*} [Finite X] (Q : SimpleGraph X)
    (I : Set X) (ind : Q.IsIndepSet I) (largest : ∀A:Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (D : ℕ) (six : 6≤D) (par : Even D) (reg : ∀x,Nat.card (Q.neighborSet x)=D)
    (N : (Q.induce Iᶜ).Subgraph) (hm:N.IsMatching) (w : ↥(Iᶜ : Set X)) (hw:w∉N.verts)
    (big:3≤(mateBlock (Q.induce Iᶜ) N w).ncard) :
    let B := Subtype.val '' (mateBlock (Q.induce Iᶜ) N w∪zeroMateRegion (Q.induce Iᶜ) N)
    D+1≤crossCount Q B Bᶜ := by
  intro B
  obtain ⟨large,small⟩ := original_preferred_region_boundary Q I ind largest D six par reg N hm w hw big
  change (D+1≤B.ncard → D+1≤crossCount Q B Bᶜ) at large
  by_cases hi : D+1≤B.ncard
  · exact large hi
  have odd := preferred_region_odd (Q.induce Iᶜ) N hm w hw
  have card : B.ncard=(mateBlock (Q.induce Iᶜ) N w∪zeroMateRegion (Q.induce Iᶜ) N).ncard :=
    Set.ncard_image_of_injective _ Subtype.val_injective
  have o := Nat.odd_iff.mp (card ▸ odd : Odd B.ncard)
  have e := Nat.even_iff.mp par
  have below : B.ncard≤D-1 := by omega
  by_contra! belowFloor
  have branches := small below (show crossCount Q B Bᶜ≤2*D by omega)
  have eq := small_region_boundary_missing Q B D (fun x _ => reg x) (by omega)
  rcases branches with ⟨d,sz,_⟩|⟨sz,_⟩
  · change B.ncard=3 at sz
    rw [d,sz] at eq
    omega
  · change B.ncard=D-1 at sz
    rw [sz,show D+1-(D-1)=2 by omega] at eq
    omega

/-- The preferred union and the other real hole blocks are counted in
one original-root budget. Only the explicit separation of the preferred
union from its companions is required beyond their known clique property. -/
theorem detached_preferred_active_count {X : Type*} [Finite X] (Q : SimpleGraph X)
    (I : Set X) (ind : Q.IsIndepSet I)
    (largest : ∀A:Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (D : ℕ) (six : 6≤D) (par : Even D) (reg : ∀x,Nat.card (Q.neighborSet x)=D)
    (N : (Q.induce Iᶜ).Subgraph) (hm:N.IsMatching)
    (maximum : N.edgeSet.ncard=matchingEdges (Q.induce Iᶜ))
    (gap : N.vertsᶜ.ncard+1=I.ncard) (noEx : exceptionalMateRegion (Q.induce Iᶜ) N=∅)
    (p : ↥(N.vertsᶜ : Set ↥(Iᶜ : Set X))) (big : 3≤(mateBlock (Q.induce Iᶜ) N p.val).ncard)
    (others : ∀j:↥(N.vertsᶜ : Set ↥(Iᶜ : Set X)),j≠p → (Q.induce Iᶜ).IsClique (mateBlock (Q.induce Iᶜ) N j.val))
    (detached : ∀j:↥(N.vertsᶜ : Set ↥(Iᶜ : Set X)),j≠p →
      ∀x∈mateBlock (Q.induce Iᶜ) N p.val∪zeroMateRegion (Q.induce Iᶜ) N,
      ∀y∈mateBlock (Q.induce Iᶜ) N j.val,¬(Q.induce Iᶜ).Adj x y) :
    let B := Subtype.val '' (mateBlock (Q.induce Iᶜ) N p.val∪zeroMateRegion (Q.induce Iᶜ) N)
    let k := {j:↥(N.vertsᶜ : Set ↥(Iᶜ : Set X)) | 3≤(mateBlock (Q.induce Iᶜ) N j.val).ncard}.ncard
    k≤2 ∧ (2*D-1≤crossCount Q B Bᶜ → k=1) ∧
      ((∃u:B,¬((Q.induce B).induce {v|v≠u}).Preconnected) → k=1) ∧
      crossCount Q B Bᶜ+(k-1)*(2*D-2)≤D*(k+1) := by
  intro B k
  classical
  let H := Q.induce Iᶜ
  let J := ↥(N.vertsᶜ : Set ↥(Iᶜ : Set X))
  let _ := Fintype.ofFinite J
  let T (j:J) := mateBlock H N j.val
  let Z := zeroMateRegion H N
  let E (j:J) := if j=p then T j∪Z else T j
  let C (j:J) : Set X := Subtype.val '' E j
  let A : Finset J := Finset.univ.filter (fun j => 3≤(T j).ncard)
  let f (j:J) := crossCount Q (C j) (C j)ᶜ
  have cmp : C p=B := by simp [C,E,B,T,Z,H]
  have pA : p∈A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,big⟩
  have aCard : A.card=k := by
    change A.card=({j:J|3≤(T j).ncard}:Set J).ncard
    rw [←Set.ncard_coe_finset]
    congr 1
    ext j;simp [A]
  have totalHoles : Fintype.card J+1=I.ncard := by
    rwa [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have hpart (x:↥(Iᶜ : Set X)) : ∃j,x∈E j := by
    rcases mate_classes_cover H N hm x with ⟨u,hu,hx⟩|hz|exceptional
    · let j : J := ⟨u,hu⟩
      refine ⟨j,?_⟩
      change x∈(if j=p then T j∪Z else T j)
      split
      · exact Or.inl hx
      · exact hx
    · refine ⟨p,?_⟩
      rw [show E p=T p∪Z from if_pos rfl]
      exact Or.inr hz
    · exact (noEx ▸ exceptional : x∈(∅ : Set ↥(Iᶜ : Set X))).elim
  have disT {i j:J} (diff:i≠j) : Disjoint (T i) (T j) :=
    different_mate_blocks_disjoint H N hm maximum i.val j.val i.property j.property (fun eq => diff (Subtype.ext eq))
  have disZ (j:J) : Disjoint (T j) Z := mate_block_disjoint_zero H N hm j.val j.property
  have dis {i j:J} (diff:i≠j) : Disjoint (E i) (E j) := by
    by_cases ip:i=p
    · have jp:j≠p := fun e => diff (ip.trans e.symm)
      rw [show E i=T i∪Z by simp [E,ip],show E j=T j by simp [E,jp]]
      exact (Set.disjoint_union_left.mpr ⟨disT diff,(disZ j).symm⟩)
    by_cases jp:j=p
    · rw [show E i=T i by simp [E,ip],show E j=T j∪Z by simp [E,jp]]
      exact (Set.disjoint_union_right.mpr ⟨disT diff,disZ i⟩)
    simpa [E,ip,jp] using disT diff
  have separate {i j:J} (diff:i≠j) : ∀x∈E i,∀y∈E j,¬H.Adj x y := by
    by_cases ip:i=p
    · subst i
      rw [show E p=T p∪Z from if_pos rfl,show E j=T j from if_neg (Ne.symm diff)]
      exact detached j (Ne.symm diff)
    by_cases jp:j=p
    · subst j
      intro x hx y hy edge
      exact detached i ip y (by simpa [E] using hy) x (by simpa [E,ip] using hx) edge.symm
    simpa [E,ip,jp,T] using clique_mate_blocks_separated H N hm maximum i.val j.val i.property j.property
      (fun eq => diff (Subtype.ext eq)) (others i ip) (others j jp)
  have external (i:J) (x:X) (hx:x∈C i) (y:X) (edge:Q.Adj x y) (out:y∉C i) : y∈I := by
    by_contra away
    obtain ⟨v,hv,rfl⟩ := hx
    let t : ↥(Iᶜ : Set X) := ⟨y,away⟩
    obtain ⟨j,hj⟩ := hpart t
    exact separate (i:=i) (j:=j) (fun eq => out ⟨t,eq.symm ▸ hj,rfl⟩) v hv t hj edge
  have total := disjoint_cut_total_budget Q C I D
    (fun _ _ diff => Set.disjoint_image_of_injective Subtype.val_injective (dis diff))
    external (fun x _ => (reg x).le)
  rw [←totalHoles] at total
  have outside (j:J) : C j⊆Iᶜ := by rintro _ ⟨x,_,rfl⟩;exact x.property
  have data (j:J) (diff:j≠p) :
      Q.IsClique (C j) ∧ Odd (C j).ncard ∧ (C j).ncard=(T j).ncard ∧ (C j).ncard≤D-1 := by
    have ej : E j=T j := if_neg diff
    have cl : Q.IsClique (C j) := by
      rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ ne
      rw [ej] at hx hy
      exact others j diff hx hy (fun eq => ne (congrArg Subtype.val eq))
    have count : (C j).ncard=(T j).ncard := (Set.ncard_image_of_injective _ Subtype.val_injective).trans (congrArg Set.ncard ej)
    have odd : Odd (C j).ncard := count ▸ mateBlock_odd H N hm j.val j.property
    have le := outside_largest_clique_size Q I (C j) ind largest (outside j) cl D (fun x => (reg x).le)
    have o := Nat.odd_iff.mp odd
    have e := Nat.even_iff.mp par
    exact ⟨cl,odd,count,by omega⟩
  have act (j:J) (member:j∈A) (diff:j≠p) : 2*D-2≤f j := by
    obtain ⟨cl,odd,eq,hi⟩ := data j diff
    exact odd_nonsingleton_clique_boundary Q (C j) D (fun x _ => reg x) cl odd
      (eq ▸ (Finset.mem_filter.mp member).2) hi
  have inact (j:J) (member:j∉A) : D≤f j := by
    obtain ⟨cl,odd,eq,hi⟩ := data j (fun same => member (same ▸ pA))
    have sz : (C j).ncard=1 := by
      have little : ¬3≤(T j).ncard := fun h => member (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      have par' := Nat.odd_iff.mp odd
      omega
    have price := clique_boundary_count Q (C j) D cl (fun x _ => reg x)
    rw [sz,Nat.one_mul] at price
    change D≤crossCount Q (C j) (C j)ᶜ
    omega
  have paid := count_paid_parts f A p pA D total act inact
  have fp : f p=crossCount Q B Bᶜ := by simp only [f,cmp]
  rw [aCard,fp] at paid
  have floor := preferred_floor Q I ind largest D six par reg N hm p.val p.property big
  have pos := Finset.card_pos.mpr (show A.Nonempty from ⟨p,pA⟩)
  rw [aCard] at pos
  have done := active_boundary_price D k (crossCount Q B Bᶜ) six pos floor paid
  refine ⟨done.1,done.2,?_,paid⟩
  rintro ⟨u,cut⟩
  apply done.2
  apply cut_vertex_boundary_of_external_neighbor Q B D reg u cut
  intro b
  have off : B⊆Iᶜ := cmp ▸ outside p
  obtain ⟨j,ji,edge⟩ := largest_independent_dominates Q I ind largest b.val (off b.property)
  exact ⟨j,fun mem => off mem ji,edge⟩

#print axioms detached_preferred_active_count
end JSP452Audit.StarHost



