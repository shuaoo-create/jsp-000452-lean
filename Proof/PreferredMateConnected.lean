import DetachedMateSizes
import BlockWithZeroRegion
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

def mateTouchesZero (H : SimpleGraph X) (N : H.Subgraph) (w : X) : Prop :=
  ∃x∈mateBlock H N w,∃z∈zeroMateRegion H N,H.Adj x z

omit [Finite X] in
/-- Two internal connected regions are joined once an edge reaches the
clique on the other side. All walks stay inside their induced union. -/
private theorem pointed_union_connected (H : SimpleGraph X) (N : H.Subgraph) (w : X)
    (clZ : H.IsClique (zeroMateRegion H N)) (touch : mateTouchesZero H N w) :
    (H.induce (mateBlock H N w ∪ zeroMateRegion H N)).Connected := by
  obtain ⟨a,atA,b,btB,edge⟩ := touch
  let A := mateBlock H N w
  let Z := zeroMateRegion H N
  let U := A∪Z
  let ar : U := ⟨a,Or.inl atA⟩
  let br : U := ⟨b,Or.inr btB⟩
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨ar,?_⟩
  intro v
  rcases v.property with inA|inZ
  · have walk := (mateBlock_connected H N w).preconnected (⟨a,atA⟩ : A) ⟨v.val,inA⟩
    exact walk.map (H.induceHomOfLE (show A⊆U from Set.subset_union_left)).toHom
  · have ab : (H.induce U).Adj ar br := edge
    by_cases eq : b=v.val
    · exact (Subtype.ext eq : br=v) ▸ ab.reachable
    · exact ab.reachable.trans (show (H.induce U).Adj br v from clZ btB inZ eq).reachable

private theorem nonclique_touches_nonempty_zero (H : SimpleGraph X) (N : H.Subgraph)
    (hm : N.IsMatching) (max : N.edgeSet.ncard=matchingEdges H) (w : X) (hw : w∉N.verts)
    (limit : ∀A:Set X,H.IsIndepSet A → A.ncard≤N.vertsᶜ.ncard+1)
    (nz : (zeroMateRegion H N).Nonempty) (bad : ¬H.IsClique (mateBlock H N w)) :
    mateTouchesZero H N w := by
  classical
  by_contra! forbid
  obtain ⟨z,zz⟩ := nz
  have small := block_with_zero_region_small H N hm max w hw limit
  apply bad
  intro x hx y hy diff
  by_contra xy
  let U := mateBlock H N w ∪ zeroMateRegion H N
  let a : U := ⟨x,Or.inl hx⟩
  let b : U := ⟨y,Or.inl hy⟩
  let c : U := ⟨z,Or.inr zz⟩
  have dis := Set.disjoint_left.mp (mate_block_disjoint_zero H N hm w hw)
  have nx : x≠z := fun eq => dis hx (eq ▸ zz)
  have ny : y≠z := fun eq => dis hy (eq ▸ zz)
  have edges := small a b c (fun e => diff (congrArg Subtype.val e))
    (fun e => nx (congrArg Subtype.val e)) (fun e => ny (congrArg Subtype.val e))
  rcases edges with e|e|e
  · exact xy e
  · exact forbid ⟨x,hx,z,zz,e⟩
  · exact forbid ⟨y,hy,z,zz,e⟩

theorem preferred_mate_zero_connected (Q : SimpleGraph X) (I : Set X) (ind : Q.IsIndepSet I)
    (largest : ∀S : Set X,Q.IsIndepSet S → S.ncard≤I.ncard)
    (D : ℕ) (evenD : Even D) (reg : ∀x,Nat.card (Q.neighborSet x)=D)
    (N : (Q.induce Iᶜ).Subgraph) (hm : N.IsMatching) (max : N.edgeSet.ncard=matchingEdges (Q.induce Iᶜ))
    (gap : N.vertsᶜ.ncard+1=I.ncard) (noEx : exceptionalMateRegion (Q.induce Iᶜ) N=∅)
    (clZ : (Q.induce Iᶜ).IsClique (zeroMateRegion (Q.induce Iᶜ) N))
    (w : ↥(Iᶜ : Set X)) (hw : w∉N.verts) (big : 3≤(mateBlock (Q.induce Iᶜ) N w).ncard)
    (pref : (∃u,u∉N.verts ∧ ¬(Q.induce Iᶜ).IsClique (mateBlock (Q.induce Iᶜ) N u)) →
      ¬(Q.induce Iᶜ).IsClique (mateBlock (Q.induce Iᶜ) N w))
    (priority : (∀u,u∉N.verts → (Q.induce Iᶜ).IsClique (mateBlock (Q.induce Iᶜ) N u)) →
      (∃u,u∉N.verts ∧ mateTouchesZero (Q.induce Iᶜ) N u) → mateTouchesZero (Q.induce Iᶜ) N w) :
    ((Q.induce Iᶜ).induce (mateBlock (Q.induce Iᶜ) N w ∪ zeroMateRegion (Q.induce Iᶜ) N)).Connected := by
  classical
  let H := Q.induce Iᶜ
  by_cases nz : (zeroMateRegion H N).Nonempty
  · apply pointed_union_connected H N w clZ
    by_cases someBad : ∃u,u∉N.verts ∧ ¬H.IsClique (mateBlock H N u)
    · have limit (S : Set ↥(Iᶜ : Set X)) (si : H.IsIndepSet S) : S.ncard≤N.vertsᶜ.ncard+1 := by
        have imageInd : Q.IsIndepSet (Subtype.val '' S) := by
          rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ ne edge
          exact si ha hb (fun eq => ne (congrArg Subtype.val eq)) edge
        have cap := largest _ imageInd
        rwa [Set.ncard_image_of_injective _ Subtype.val_injective,←gap] at cap
      exact nonclique_touches_nonempty_zero H N hm max w hw limit nz (pref someBad)
    · have all (u : ↥(Iᶜ : Set X)) (hu : u∉N.verts) : H.IsClique (mateBlock H N u) := by
        by_contra h;exact someBad ⟨u,hu,h⟩
      apply priority all
      by_contra! none
      have separate (u : ↥(Iᶜ : Set X)) (hu : u∉N.verts) (a) (ha : a∈mateBlock H N u)
          (b) (hb : b∈zeroMateRegion H N) : ¬H.Adj a b :=
        fun edge => none u hu ⟨a,ha,b,hb,edge⟩
      obtain one|d := detached_mate_sizes Q I ind largest D reg N hm max gap noEx nz clZ all separate w hw
      · omega
      · have odd := mateBlock_odd H N hm w hw
        rw [d] at odd
        exact Nat.not_even_iff_odd.mpr odd evenD
  · have zero := Set.not_nonempty_iff_eq_empty.mp nz
    change (H.induce (mateBlock H N w∪zeroMateRegion H N)).Connected
    rw [zero,Set.union_empty]
    exact mateBlock_connected H N w

#print axioms preferred_mate_zero_connected
end JSP452Audit.StarHost
