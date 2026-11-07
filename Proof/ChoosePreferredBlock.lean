import PreferredMateConnected
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private theorem nontrivial_of_nonclique (H : SimpleGraph X) (N : H.Subgraph) (hm : N.IsMatching)
    (w : X) (hw : w∉N.verts) (bad : ¬H.IsClique (mateBlock H N w)) :
    3≤(mateBlock H N w).ncard := by
  have odd := Nat.odd_iff.mp (mateBlock_odd H N hm w hw)
  by_contra! small
  have narrow : (mateBlock H N w).ncard≤1 := by omega
  exact bad (fun {a} ha {b} hb ne => (ne ((Set.ncard_le_one (Set.toFinite _)).mp narrow a ha b hb)).elim)

private theorem nontrivial_of_contact (H : SimpleGraph X) (N : H.Subgraph) (hm : N.IsMatching)
    (w : X) (hw : w∉N.verts) (touch : mateTouchesZero H N w) :
    3≤(mateBlock H N w).ncard := by
  obtain ⟨a,ha,z,⟨y,zy,away,_⟩,az⟩ := touch
  have ne : w≠a := fun eq => away w hw (eq.symm ▸ az.symm)
  have more := (Set.one_lt_ncard_iff (Set.toFinite _)).mpr
    ⟨w,a,mateBlock_self H N w,ha,ne⟩
  have odd := Nat.odd_iff.mp (mateBlock_odd H N hm w hw)
  omega

/-- Select an actual nontrivial preferred root. Its block joined with the
zero region is connected, and all remaining pointed blocks are cliques. -/
theorem exists_preferred_connected_block (Q : SimpleGraph X) (I : Set X) (ind : Q.IsIndepSet I)
    (largest : ∀S : Set X,Q.IsIndepSet S → S.ncard≤I.ncard)
    (D : ℕ) (evenD : Even D) (reg : ∀x,Nat.card (Q.neighborSet x)=D)
    (N : (Q.induce Iᶜ).Subgraph) (hm : N.IsMatching) (max : N.edgeSet.ncard=matchingEdges (Q.induce Iᶜ))
    (gap : N.vertsᶜ.ncard+1=I.ncard) (noEx : exceptionalMateRegion (Q.induce Iᶜ) N=∅)
    (clZ : (Q.induce Iᶜ).IsClique (zeroMateRegion (Q.induce Iᶜ) N))
    (anyBig : ∃w,w∉N.verts ∧ 3≤(mateBlock (Q.induce Iᶜ) N w).ncard) :
    let H := Q.induce Iᶜ
    ∃w,w∉N.verts ∧ 3≤(mateBlock H N w).ncard ∧
      (H.induce (mateBlock H N w ∪ zeroMateRegion H N)).Connected ∧
      ∀u,u∉N.verts → u≠w → H.IsClique (mateBlock H N u) := by
  intro H
  classical
  have limit (S : Set ↥(Iᶜ : Set X)) (si : H.IsIndepSet S) : S.ncard≤N.vertsᶜ.ncard+1 := by
    have imageInd : Q.IsIndepSet (Subtype.val '' S) := by
      rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ ne edge
      exact si ha hb (fun eq => ne (congrArg Subtype.val eq)) edge
    have cap := largest _ imageInd
    rwa [Set.ncard_image_of_injective _ Subtype.val_injective,←gap] at cap
  have solve (w) (hw : w∉N.verts) (big : 3≤(mateBlock H N w).ncard)
      (preferred : (∃u,u∉N.verts ∧ ¬H.IsClique (mateBlock H N u)) → ¬H.IsClique (mateBlock H N w))
      (top : (∀u,u∉N.verts → H.IsClique (mateBlock H N u)) →
        (∃u,u∉N.verts ∧ mateTouchesZero H N u) → mateTouchesZero H N w) :
      (H.induce (mateBlock H N w ∪ zeroMateRegion H N)).Connected ∧
      ∀u,u∉N.verts → u≠w → H.IsClique (mateBlock H N u) := by
    exact ⟨preferred_mate_zero_connected Q I ind largest D evenD reg N hm max gap noEx clZ
      w hw big preferred top,other_mate_blocks_clique_of_preferred H N hm max limit w hw preferred⟩
  by_cases bad : ∃u,u∉N.verts ∧ ¬H.IsClique (mateBlock H N u)
  · obtain ⟨w,hw,bw⟩ := bad
    have big := nontrivial_of_nonclique H N hm w hw bw
    exact ⟨w,hw,big,solve w hw big (fun _ => bw) (fun all _ => (bw (all w hw)).elim)⟩
  · by_cases contact : ∃u,u∉N.verts ∧ mateTouchesZero H N u
    · obtain ⟨w,hw,touch⟩ := contact
      have big := nontrivial_of_contact H N hm w hw touch
      exact ⟨w,hw,big,solve w hw big (fun h => (bad h).elim) (fun _ _ => touch)⟩
    · obtain ⟨w,hw,big⟩ := anyBig
      exact ⟨w,hw,big,solve w hw big (fun h => (bad h).elim) (fun _ h => (contact h).elim)⟩

#print axioms exists_preferred_connected_block
end JSP452Audit.StarHost
