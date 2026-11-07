import FailureNormalization

namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- All finite host and target data of a strict source in one universe; the
two original lists are part of the object rather than fixed parameters. -/
structure StrictFamily where
  X : Type u
  [finiteX : Finite X]
  G : SimpleGraph X
  s : ℕ
  t : ℕ
  r : ℕ
  n : Fin s → ℕ
  m : Fin t → ℕ
  hs : 0 < s
  ht : 0 < t
  hn : Antitone n
  hm : Antitone m
  pn : ∀ i, 1 ≤ n i
  pm : ∀ j, 1 ≤ m j
  live : 0 < rowCount s t r
  row : ForcingRow G s t (padDemand n) (padDemand m) r
  strict : G.edgeSet.ncard < rowEnergy n m r

attribute [instance] StrictFamily.finiteX

def StrictFamily.rank (F : StrictFamily) : ℕ := rowCount F.s F.t F.r
noncomputable def StrictFamily.edges (F : StrictFamily) : ℕ := F.G.edgeSet.ncard
noncomputable def StrictFamily.order (F : StrictFamily) : ℕ := Nat.card F.X

private theorem minimum_nat_key {B : Type*} (key : B → ℕ) (start : B) :
    ∃ b : B, ∀ a : B, key b ≤ key a := by
  classical
  have available : ∃ n : ℕ, ∃ b : B, key b = n := ⟨key start,start,rfl⟩
  obtain ⟨b,eq⟩ := Nat.find_spec available
  exact ⟨b,fun a => eq.trans_le (Nat.find_min' available ⟨a,rfl⟩)⟩

/-- Among *all* strict families choose successive true minima in rank, number
of edges and order. Smaller-rank competitors may change every graph and list. -/
theorem exists_global_minimal_strict (start : StrictFamily.{u}) :
    ∃ F : StrictFamily.{u},
      (∀ B : StrictFamily.{u}, F.rank ≤ B.rank) ∧
      (∀ B : StrictFamily.{u}, B.rank=F.rank → F.edges ≤ B.edges) ∧
      (∀ B : StrictFamily.{u}, B.rank=F.rank → B.edges=F.edges → F.order ≤ B.order) := by
  obtain ⟨first,minRank⟩ := minimum_nat_key StrictFamily.rank start
  let RankSet := {B : StrictFamily.{u} // B.rank=first.rank}
  obtain ⟨second,minEdges⟩ := minimum_nat_key (fun B : RankSet => B.val.edges) ⟨first,rfl⟩
  let Both := {B : RankSet // B.val.edges=second.val.edges}
  obtain ⟨third,minOrder⟩ := minimum_nat_key (fun B : Both => B.val.val.order) ⟨second,rfl⟩
  let F := third.val.val
  have rank : F.rank = first.rank := third.val.property
  have edges : F.edges = second.val.edges := third.property
  refine ⟨F,fun B => rank.trans_le (minRank B),?_,?_⟩
  · intro B hr
    exact edges.trans_le (minEdges ⟨B,hr.trans rank⟩)
  · intro B hr he
    exact minOrder ⟨⟨B,hr.trans rank⟩,he.trans edges⟩

/-- Failure of the *original* size Ramsey equality supplies a strict source
at the entry row, in every requested host universe by an actual graph iso. -/
theorem strictFamily_of_failure {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1≤n i) (pm : ∀ j, 1≤m j)
    (fail : sizeRamsey (forest n) (forest m) ≠ ∑ k ∈ Finset.Icc 2 (s+t), diagonal n m k) :
    Nonempty StrictFamily.{u} := by
  obtain ⟨N,G,edge,forces⟩ := star_min_attained n m
  have upper := erdos561_upper n m
  have less : G.edgeSet.ncard < rowEnergy n m 0 := by rw [edge,rowEnergy_zero]; omega
  let L := ULift.{u} (Fin N)
  let Y : SimpleGraph L := G.comap ULift.down
  let iso : G ≃g Y := {toEquiv := Equiv.ulift.symm, map_rel_iff' := Iff.rfl}
  have equalEdges : G.edgeSet.ncard = Y.edgeSet.ncard := Nat.card_congr iso.mapEdgeSet
  exact ⟨{X := L, G := Y,s:=s,t:=t,r:=0,n:=n,m:=m,hs:=hs,ht:=ht,hn:=hn,hm:=hm,pn:=pn,pm:=pm,
          live := by dsimp [rowCount]; omega
          row := forcingRow_of_iso iso ((finite_targets_row_zero G hs ht n m).mpr forces)
          strict := equalEdges ▸ less}⟩

#print axioms exists_global_minimal_strict
#print axioms strictFamily_of_failure
end JSP452Audit.StarHost
