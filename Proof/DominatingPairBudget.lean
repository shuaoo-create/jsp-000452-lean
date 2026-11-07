import AlmostHalfPerfect
import PairCutDegrees
open private JSP452Audit.StarHost.remove_one_count from PairCutDegrees

namespace JSP452Audit.StarHost
open SimpleGraph
set_option maxHeartbeats 1000000

private theorem dp_triple_degree {X : Type*} [Finite X]
    (Q : SimpleGraph X) [DecidableRel Q.Adj] (x y z : X)
    (xy : x≠y) (xz : x≠z) (yz : y≠z)
    (w : ↥(({x,y,z} : Set X)ᶜ)) :
    Nat.card ((Q.induce ({x,y,z} : Set X)ᶜ).neighborSet w) +
      (if Q.Adj w.val x then 1 else 0) + (if Q.Adj w.val y then 1 else 0) +
      (if Q.Adj w.val z then 1 else 0) = Nat.card (Q.neighborSet w.val) := by
  classical
  let N := Q.neighborSet w.val
  let V := ((N \ {x}) \ {y}) \ {z}
  let e : ((Q.induce ({x,y,z} : Set X)ᶜ).neighborSet w) ≃ ↥V := {
    toFun := fun u => ⟨u.val.val,⟨⟨u.property,fun h => u.val.property (by
      exact Or.inl (Set.mem_singleton_iff.mp h))⟩,fun h => u.val.property (by
        exact Or.inr (Or.inl (Set.mem_singleton_iff.mp h)))⟩,
      fun h => u.val.property (Or.inr (Or.inr h))⟩
    invFun := fun u => ⟨⟨u.val,by
      rintro (h|h|h)
      · exact u.property.1.1.2 (Set.mem_singleton_iff.mpr h)
      · exact u.property.1.2 (Set.mem_singleton_iff.mpr h)
      · exact u.property.2 h⟩,u.property.1.1.1⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have first := JSP452Audit.StarHost.remove_one_count N x
  have second := JSP452Audit.StarHost.remove_one_count (N \ {x}) y
  have third := JSP452Audit.StarHost.remove_one_count ((N \ {x}) \ {y}) z
  have mx : x∈N ↔ Q.Adj w.val x := Iff.rfl
  have my : y∈N \ {x} ↔ Q.Adj w.val y := by simp [N,xy.symm]
  have mz : z∈(N \ {x}) \ {y} ↔ Q.Adj w.val z := by simp [N,xz.symm,yz.symm]
  simp only [mx] at first
  simp only [my] at second
  simp only [mz] at third
  rw [Nat.card_congr e,Nat.card_coe_set_eq]
  change V.ncard+_+_+_=N.ncard
  dsimp [V]
  omega

private theorem dp_common_count {X : Type*} [Finite X] (Q : SimpleGraph X)
    [DecidableRel Q.Adj] (D : ℕ) (regular : ∀w,Nat.card (Q.neighborSet w)=D)
    (x y : X) (xy : x≠y)
    (dominate : ∀w,w≠x→w≠y→Q.Adj w x ∨ Q.Adj w y) :
    (Q.neighborSet x ∩ Q.neighborSet y).ncard + (Nat.card X-2) +
      2*(if Q.Adj x y then 1 else 0) = 2*D := by
  classical
  let A := Q.neighborSet x \ {y}
  let B := Q.neighborSet y \ {x}
  have union : A ∪ B = ({x,y} : Set X)ᶜ := by
    ext w
    constructor
    · rintro (ha|hb)
      · exact fun h => h.elim (fun eq => (show Q.Adj x w from ha.1).ne eq.symm) ha.2
      · exact fun h => h.elim (fun eq => hb.2 (Set.mem_singleton_iff.mpr eq))
          (fun eq => (show Q.Adj y w from hb.1).ne (Set.mem_singleton_iff.mp eq).symm)
    · intro outside
      have wx : w≠x := fun h => outside (Or.inl h)
      have wy : w≠y := fun h => outside (Or.inr (Set.mem_singleton_iff.mpr h))
      exact (dominate w wx wy).elim
        (fun h => Or.inl ⟨h.symm,wy⟩) (fun h => Or.inr ⟨h.symm,wx⟩)
  have inter : A ∩ B = Q.neighborSet x ∩ Q.neighborSet y := by
    ext w
    constructor
    · exact fun h => ⟨h.1.1,h.2.1⟩
    · intro h
      exact ⟨⟨h.1,(show Q.Adj y w from h.2).ne.symm⟩,
        ⟨h.2,(show Q.Adj x w from h.1).ne.symm⟩⟩
  have aCount := JSP452Audit.StarHost.remove_one_count (Q.neighborSet x) y
  have bCount := JSP452Audit.StarHost.remove_one_count (Q.neighborSet y) x
  have adjacent : x∈Q.neighborSet y ↔ Q.Adj x y := Q.adj_comm y x
  have adjacent' : y∈Q.neighborSet x ↔ Q.Adj x y := Iff.rfl
  simp only [adjacent,adjacent'] at aCount bCount
  have regX : (Q.neighborSet x).ncard=D := regular x
  have regY : (Q.neighborSet y).ncard=D := regular y
  have pair : ({x,y} : Set X).ncard=2 := by simp [xy]
  have account := Set.ncard_union_add_ncard_inter A B
  rw [union,inter,Set.ncard_compl,pair] at account
  rw [regX] at aCount
  rw [regY] at bCount
  change A.ncard+_=D at aCount
  change B.ncard+_=D at bCount
  omega

/-- A two-vertex dominating set in an odd regular graph supplies a common
neighbor whose simultaneous deletion leaves a perfect matching on the
unchanged original labels. No factor-criticality or classification is assumed. -/
theorem dominating_pair_triple_perfect {X : Type*} [Finite X] (Q : SimpleGraph X)
    (D : ℕ) (large : 4≤D) (odd : Odd (Nat.card X))
    (regular : ∀w,Nat.card (Q.neighborSet w)=D) (x y : X) (xy : x≠y)
    (dominate : ∀w,w≠x→w≠y→Q.Adj w x ∨ Q.Adj w y) :
    ∃ z, Q.Adj z x ∧ Q.Adj z y ∧
      ∃ M : (Q.induce ({x,y,z} : Set X)ᶜ).Subgraph, M.IsPerfectMatching := by
  classical
  let C := Q.neighborSet x ∩ Q.neighborSet y
  let e : ℕ := if Q.Adj x y then 1 else 0
  have boundE : e≤1 := by dsimp [e]; split <;> omega
  have boundN := Set.ncard_le_ncard
    (show Q.neighborSet x ⊆ ({x} : Set X)ᶜ from
      fun w h => fun eq => (show Q.Adj x w from h).ne (Set.mem_singleton_iff.mp eq).symm)
  rw [Set.ncard_compl,Set.ncard_singleton] at boundN
  have regX : (Q.neighborSet x).ncard=D := regular x
  have mod := Nat.odd_iff.mp odd
  obtain ⟨r,order⟩ : ∃r:ℕ,Nat.card X=2*r+3 := by
    refine ⟨(Nat.card X-3)/2,?_⟩
    omega
  have positive : 0<r := by omega
  have common := dp_common_count Q D regular x y xy dominate
  change C.ncard+(Nat.card X-2)+2*e=2*D at common
  have present : 0<C.ncard := by omega
  obtain ⟨z,hz⟩ := (Set.ncard_pos (Set.toFinite C)).mp present
  have zx : Q.Adj z x := hz.1.symm
  have zy : Q.Adj z y := hz.2.symm
  have xz : x≠z := zx.ne.symm
  have yz : y≠z := zy.ne.symm
  let U : Set X := {x,y,z}
  let H := Q.induce Uᶜ
  have three : U.ncard=3 := by simp [U,xy,xz,yz]
  have hOrder : Nat.card ↥(Uᶜ : Set X)=2*r := by
    rw [Nat.card_coe_set_eq,Set.ncard_compl,three,order]
    omega
  have counts (w : ↥(Uᶜ : Set X)) :
      Nat.card (H.neighborSet w)+(if Q.Adj w.val x then 1 else 0)+
        (if Q.Adj w.val y then 1 else 0)+(if Q.Adj w.val z then 1 else 0)=D :=
    (dp_triple_degree Q x y z xy xz yz w).trans (regular w.val)
  have losses (w : ↥(Uᶜ : Set X)) : D-3≤Nat.card (H.neighborSet w) := by
    have ct := counts w
    split_ifs at ct <;> omega
  have outside (w : ↥(Uᶜ : Set X)) : w.val≠x ∧ w.val≠y ∧ w.val≠z := by
    have mem := w.property
    simpa only [U,Set.mem_compl_iff,Set.mem_insert_iff,Set.mem_singleton_iff,not_or] using mem
  have boundR : r≤D-1 := by omega
  have smaller : ∀w, r-1≤Nat.card (H.neighborSet w) := by
    intro w
    have ct := counts w
    have ⟨wx,wy,wz⟩ := outside w
    by_cases room : r≤D-2
    · have loss := losses w; omega
    · have last : r=D-1 := by omega
      have unique : C.ncard=1 := by omega
      have notBoth : ¬(Q.Adj w.val x ∧ Q.Adj w.val y) := by
        intro both
        have inC : w.val∈C := ⟨both.1.symm,both.2.symm⟩
        exact wz ((Set.ncard_le_one (Set.toFinite C)).mp unique.le w.val inC z hz)
      by_cases hx : Q.Adj w.val x
      · have hy : ¬Q.Adj w.val y := fun hy => notBoth ⟨hx,hy⟩
        simp only [if_pos hx,if_neg hy] at ct
        split_ifs at ct <;> omega
      · simp only [if_neg hx] at ct
        split_ifs at ct <;> omega
  have lowLabelBound (A : Set X)
      (into : ∀w:↥(Uᶜ : Set X), Nat.card (H.neighborSet w)=r-1 → w.val∈A) :
      {w | Nat.card (H.neighborSet w)=r-1}.ncard≤A.ncard := by
    let f (w : {w | Nat.card (H.neighborSet w)=r-1}) : A := ⟨w.val.val,into w.val w.property⟩
    have inj : Function.Injective f := fun _ _ eq => Subtype.ext (Subtype.ext
      (congrArg (fun a:A => a.val) eq))
    simpa only [Nat.card_coe_set_eq] using Nat.card_le_card_of_injective f inj
  have lowCount : {w | Nat.card (H.neighborSet w)=r-1}.ncard≤r := by
    by_cases room : r≤D-3
    · have empty : {w | Nat.card (H.neighborSet w)=r-1}=∅ := by
        ext w
        simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
        have loss := losses w
        omega
      rw [empty,Set.ncard_empty]; omega
    · by_cases next : r=D-2
      · have into : ∀w:↥(Uᶜ : Set X),Nat.card (H.neighborSet w)=r-1 → w.val∈C \ {z} := by
          intro w low
          have ct := counts w
          have ⟨wx,wy,wz⟩ := outside w
          have both : Q.Adj w.val x ∧ Q.Adj w.val y := by
            constructor
            · by_contra no
              simp only [if_neg no] at ct
              split_ifs at ct <;> omega
            · by_contra no
              simp only [if_neg no] at ct
              split_ifs at ct <;> omega
          exact ⟨⟨both.1.symm,both.2.symm⟩,wz⟩
        have count := lowLabelBound (C \ {z}) into
        have card := Set.ncard_sdiff_singleton_add_one hz
        omega
      · have last : r=D-1 := by omega
        have unique : C.ncard=1 := by omega
        have into : ∀w:↥(Uᶜ : Set X),Nat.card (H.neighborSet w)=r-1 →
            w.val∈Q.neighborSet z \ {x,y} := by
          intro w low
          have ct := counts w
          have ⟨wx,wy,wz⟩ := outside w
          have yes : Q.Adj w.val z := by
            by_contra no
            have both : Q.Adj w.val x ∧ Q.Adj w.val y := by
              constructor
              · by_contra noX
                simp only [if_neg noX,if_neg no] at ct
                split_ifs at ct <;> omega
              · by_contra noY
                simp only [if_neg noY,if_neg no] at ct
                split_ifs at ct <;> omega
            have inC : w.val∈C := ⟨both.1.symm,both.2.symm⟩
            exact wz ((Set.ncard_le_one (Set.toFinite C)).mp unique.le w.val inC z hz)
          exact ⟨yes.symm,by simp [wx,wy]⟩
        have count := lowLabelBound (Q.neighborSet z \ {x,y}) into
        have sub : ({x,y} : Set X)⊆Q.neighborSet z := by
          intro w hw; rcases hw with h|h
          · exact h.symm ▸ zx
          · exact (Set.mem_singleton_iff.mp h).symm ▸ zy
        have card := Set.ncard_sdiff_add_ncard_of_subset sub
        have pair : ({x,y} : Set X).ncard=2 := by simp [xy]
        have regZ : (Q.neighborSet z).ncard=D := regular z
        rw [pair,regZ] at card
        omega
  exact ⟨z,zx,zy,almost_half_degree_perfect H r positive hOrder smaller lowCount⟩

/-- Delete the two original dominating labels and retain the matching from
the triple-deletion witness. Its only exposed vertex is a common neighbor,
so every remaining full-degree vertex is covered by that same matching. -/
theorem dominating_pair_budget {X : Type*} [Finite X] (Q : SimpleGraph X)
    (D : ℕ) (large : 4≤D) (odd : Odd (Nat.card X))
    (regular : ∀w,Nat.card (Q.neighborSet w)=D) (x y : X) (xy : x≠y)
    (dominate : ∀w,w≠x→w≠y→Q.Adj w x ∨ Q.Adj w y) :
    deletionBudget Q (D-1)≤2 := by
  classical
  obtain ⟨z,zx,zy,M,perfect⟩ := dominating_pair_triple_perfect Q D large odd regular x y xy dominate
  let U : Set X := {x,y}
  let V : Set X := {x,y,z}
  let H := Q.induce Uᶜ
  let K := Q.induce Vᶜ
  let incl : K ↪g H := {
    toFun := fun w => ⟨w.val,by
      intro mem
      exact w.property (mem.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl (Set.mem_singleton_iff.mp h))))⟩
    inj' := fun _ _ eq => Subtype.ext (congrArg (fun a : ↥(Uᶜ : Set X) => a.val) eq)
    map_rel_iff' := Iff.rfl }
  let N := M.map incl.toHom
  have counts (w : ↥(Uᶜ : Set X)) :
      Nat.card (H.neighborSet w)+(if Q.Adj w.val x then 1 else 0)+
        (if Q.Adj w.val y then 1 else 0)=D :=
    (degree_after_pair_cut Q xy w).trans (regular w.val)
  have bound (w : ↥(Uᶜ : Set X)) : Nat.card (H.neighborSet w)≤D-1 := by
    have ct := counts w
    have wx : w.val≠x := fun eq => w.property (Or.inl eq)
    have wy : w.val≠y := fun eq => w.property (Or.inr (Set.mem_singleton_iff.mpr eq))
    rcases dominate w.val wx wy with hx|hy
    · simp only [if_pos hx] at ct; split_ifs at ct <;> omega
    · simp only [if_pos hy] at ct; split_ifs at ct <;> omega
  have covers (w : ↥(Uᶜ : Set X)) (full : Nat.card (H.neighborSet w)=D-1) : w∈N.verts := by
    have wz : w.val≠z := by
      intro eq
      have ct := counts w
      rw [eq] at ct
      simp only [if_pos zx,if_pos zy] at ct
      omega
    let v : ↥(Vᶜ : Set X) := ⟨w.val,by
      rintro (h|h|h)
      · exact w.property (Or.inl h)
      · exact w.property (Or.inr (Set.mem_singleton_iff.mpr h))
      · exact wz (Set.mem_singleton_iff.mp h)⟩
    exact ⟨v,perfect.2 v,rfl⟩
  have witness := admits_remainder_of_full_cover H (D-1) (by omega) bound N
    (perfect.1.map incl.toHom incl.injective) covers
  have card : U.ncard=2 := by simp [U,xy]
  exact (deletionBudget_le_of_witness Q (D-1) U witness).trans_eq card

#print axioms dominating_pair_triple_perfect
#print axioms dominating_pair_budget
end JSP452Audit.StarHost

