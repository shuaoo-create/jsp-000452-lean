import SplitRootBoundFromFour
import OriginalSplitBudget
import ActualCutPartition
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private theorem cliff_size (Q : SimpleGraph X) (I : Set X)
    (ind : Q.IsIndepSet I) (largest : ∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (D : ℕ) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (x : ↥(Iᶜ : Set X)) (S : Set ↥(Iᶜ : Set X))
    (cl : (Q.induce Iᶜ).IsClique S) (off : x∉S) (near : ∃a∈S,(Q.induce Iᶜ).Adj x a) :
    S.ncard≤D-1 := by
  obtain ⟨a,ha,xa⟩ := near
  obtain ⟨i,hi,ai⟩ := largest_independent_dominates Q I ind largest a.val a.property
  let C : Set X := Subtype.val '' S
  have clC : Q.IsClique C := by
    rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩ ne
    exact cl hu hv (fun eq => ne (congrArg Subtype.val eq))
  have hx : x.val ∉ C := by
    rintro ⟨z,hz,eq⟩;exact off ((Subtype.ext eq : z=x) ▸ hz)
  have ih : i∉C := by rintro ⟨z,_,rfl⟩;exact z.property hi
  have ne : x.val≠i := fun eq => x.property (eq.symm ▸ hi)
  have bound := clique_size_with_two_exits Q C clC D reg (show a.val∈C from ⟨a,ha,rfl⟩)
    hx ih ne xa.symm ai
  rwa [show C.ncard=S.ncard from Set.ncard_image_of_injective _ Subtype.val_injective] at bound

/-- On the actual residual graph of Q, a genuine crossing forces a three-point
preferred path and exactly one other nontrivial block, a D−1 clique. -/
theorem crossing_forces_three_path_from_four (Q : SimpleGraph X) (I : Set X)
    (ind : Q.IsIndepSet I) (largest : ∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (D : ℕ) (four : 4≤D) (par : Even D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (N : (Q.induce Iᶜ).Subgraph) (hm : N.IsMatching)
    (max : N.edgeSet.ncard=matchingEdges (Q.induce Iᶜ))
    (gap : N.vertsᶜ.ncard+1=I.ncard) (noEx : exceptionalMateRegion (Q.induce Iᶜ) N=∅)
    (p q : ↥(N.vertsᶜ : Set ↥(Iᶜ : Set X))) (qp : q≠p)
    (conn : ((Q.induce Iᶜ).induce (mateBlock (Q.induce Iᶜ) N p.val∪zeroMateRegion (Q.induce Iᶜ) N)).Preconnected)
    (others : ∀j : ↥(N.vertsᶜ : Set ↥(Iᶜ : Set X)), j≠p → (Q.induce Iᶜ).IsClique (mateBlock (Q.induce Iᶜ) N j.val))
    (x : ↥(mateBlock (Q.induce Iᶜ) N p.val∪zeroMateRegion (Q.induce Iᶜ) N))
    (y : mateBlock (Q.induce Iᶜ) N q.val) (edge : (Q.induce Iᶜ).Adj x.val y.val) :
    let H := Q.induce Iᶜ
    let P := mateBlock H N p.val∪zeroMateRegion H N
    ∃ l r : ↥(Iᶜ : Set X), l≠r ∧ l≠x.val ∧ r≠x.val ∧ P={x.val,l,r} ∧
      H.Adj x.val l ∧ H.Adj x.val r ∧ ¬H.Adj l r ∧
      (mateBlock H N q.val).ncard=D-1 ∧
      ∀j : ↥(N.vertsᶜ : Set ↥(Iᶜ : Set X)), j≠p → j≠q → (mateBlock H N j.val).ncard=1 := by
  intro H P
  classical
  let J := ↥(N.vertsᶜ : Set ↥(Iᶜ : Set X))
  let _ := Fintype.ofFinite J
  let W := preferredMatePart H N p
  have limit (S : Set ↥(Iᶜ : Set X)) (si : H.IsIndepSet S) : S.ncard≤N.vertsᶜ.ncard+1 := by
    have imageInd : Q.IsIndepSet (Subtype.val '' S) := by
      rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ ne edge
      exact si ha hb (fun eq => ne (congrArg Subtype.val eq)) edge
    have cap := largest _ imageInd
    rwa [Set.ncard_image_of_injective _ Subtype.val_injective,←gap] at cap
  obtain ⟨L,R,_,_,lr,sides,xl,xr,apart,cl,off,cover,sep⟩ :=
    actual_cross_partition H N hm max noEx p q qp conn limit others x y edge
  let F := splitCutParts W p L R
  have left : F (some p)=L := by simp [F,splitCutParts]
  have right : F none=R := rfl
  have plain (j:J) (ip:j≠p) : F (some j)=mateBlock H N j.val := by
    simp [F,splitCutParts,W,preferredMatePart,ip]
  have sizes (i:Option J) : 1≤(F i).ncard ∧ (F i).ncard≤D-1 := by
    cases i with
    | none =>
      exact ⟨(Set.ncard_pos (Set.toFinite _)).mpr ⟨xr.choose,xr.choose_spec.1⟩,
        cliff_size Q I ind largest D reg x.val R (cl none) (off none) xr⟩
    | some j =>
      by_cases ip:j=p
      · subst j
        rw [left]
        exact ⟨(Set.ncard_pos (Set.toFinite _)).mpr ⟨xl.choose,xl.choose_spec.1⟩,
          cliff_size Q I ind largest D reg x.val L (left ▸ cl (some p)) (left ▸ off (some p)) xl⟩
      rw [plain j ip]
      let T := mateBlock H N j.val
      let C : Set X := Subtype.val '' T
      have clC : Q.IsClique C := by
        rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩ ne
        exact others j ip hu hv (fun eq => ne (congrArg Subtype.val eq))
      have outside : C⊆Iᶜ := by rintro _ ⟨u,_,rfl⟩;exact u.property
      have bound := outside_largest_clique_size Q I C ind largest outside clC D (fun u => (reg u).le)
      rw [show C.ncard=T.ncard from Set.ncard_image_of_injective _ Subtype.val_injective] at bound
      have odd := Nat.odd_iff.mp (mateBlock_odd H N hm j.val j.property)
      have evenD := Nat.even_iff.mp par
      change (mateBlock H N j.val).ncard≤D at bound
      exact ⟨by omega,by omega⟩
  have count : I.ncard=Fintype.card (Option J) := by
    rw [Fintype.card_option,←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
    exact gap.symm
  have big := crossing_companion_big H N hm max p.val q.val p.property q.property
    (fun eq => qp (Subtype.ext eq.symm)) x y edge
  have eqs := original_split_clique_sizes_from_four Q I ind largest D four reg x.val F count
    apart off cover cl sep sizes (some q) (by rw [plain q qp];exact big)
  have lcard : L.ncard=1 := left ▸ eqs.2 (some p) (by simp [Ne.symm qp])
  have rcard : R.ncard=1 := eqs.2 none (by simp)
  obtain ⟨l,hl,xl'⟩ := xl
  obtain ⟨r,hr,xr'⟩ := xr
  have leq : L={l} := by
    ext v; constructor
    · intro hv
      exact Set.mem_singleton_iff.mpr ((Set.ncard_le_one (Set.toFinite _)).mp lcard.le v hv l hl)
    · intro h;exact (Set.mem_singleton_iff.mp h).symm ▸ hl
  have req : R={r} := by
    ext v; constructor
    · intro hv
      exact Set.mem_singleton_iff.mpr ((Set.ncard_le_one (Set.toFinite _)).mp rcard.le v hv r hr)
    · intro h;exact (Set.mem_singleton_iff.mp h).symm ▸ hr
  have neq : l≠r := fun e => Set.disjoint_left.mp lr hl (e.symm ▸ hr)
  have form : P={x.val,l,r} := by
    rw [leq,req] at sides
    ext v
    by_cases same : v=x.val
    · subst v; simp
    · have iff := Set.ext_iff.mp sides v
      simp [same,P] at iff ⊢
      tauto
  refine ⟨l,r,neq,xl'.ne.symm,xr'.ne.symm,form,xl',xr',?_,?_,?_⟩
  · have hleft : l∈F (some p) := by rw [left];exact hl
    exact sep (some p) none (by simp) l hleft r hr
  · exact plain q qp ▸ eqs.1
  · intro j jp jq
    exact plain j jp ▸ eqs.2 (some j) (by simpa using jq)

#print axioms crossing_forces_three_path_from_four
end JSP452Audit.StarHost
