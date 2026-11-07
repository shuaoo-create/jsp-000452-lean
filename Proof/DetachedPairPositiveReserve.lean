import SingleRootOwnerObstruction
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] [Nonempty X]

theorem detached_pair_positive_reserve (Q : SimpleGraph X) (I : Set X) (ind : Q.IsIndepSet I)
    (largest : ∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (D : ℕ) (six : 6≤D) (par : Even D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (crit : PerfectAfterEveryDeletion Q) (s : DetachedMatePair (Q.induce Iᶜ))
    (count : s.singles.ncard+3=I.ncard)
    (small : NoIndependentTriple ((Q.induce Iᶜ).induce s.preferred)) :
    1≤baseReserve Q D := by
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
  have op : Odd P.ncard := (Set.ncard_image_of_injective _ Subtype.val_injective).symm ▸ s.preferred_odd
  have oc : Odd C.ncard := (Set.ncard_image_of_injective _ Subtype.val_injective).symm ▸ s.companion_odd
  obtain ⟨critical,⟨z,_,single⟩⟩ := detached_pair_root_profile Q I ind largest D six par reg s count small
  have size : P.ncard=D+1 := (detached_pair_exact_prices Q I ind largest D six par reg s count).1
  by_contra! fail
  have zero : baseReserve Q D=0 := by omega
  have pairs (i:X) (hi:i∈I) : ∃u∈I,∀v∈P,Q.Adj i v ∨ Q.Adj u v := by
    obtain ⟨V,perf⟩ := crit i
    obtain ⟨M,hm,supp,_⟩ := lift_perfect_off_vertex_maximum Q i V perf
    obtain ⟨u,hu,ui,p,hp,up,unique⟩ := unique_preferred_matching_exit Q I S P C ind i hi M hm supp
      liftCount (Set.disjoint_image_of_injective Subtype.val_injective s.sp)
      (Set.disjoint_image_of_injective Subtype.val_injective s.sc)
      (Set.disjoint_image_of_injective Subtype.val_injective s.apart)
      (outside _) (outside _) (outside _) op oc singles pExt cExt
    refine ⟨u,hu,?_⟩
    intro v hv
    apply roots_cover_exposable_points Q D (by omega) reg crit zero M hm i u ui
      (fun e => ind hi hu ui.symm e) P (fun h => outside _ h hi) (fun h => outside _ h hu)
      supp p hp up (fun t ht w e out => unique t ht w (pExt t ht w (M.adj_sub e) out) e)
      ⟨v,hv⟩ (critical ⟨v,hv⟩)
  exact full_single_root_profile_impossible Q I P D six par reg crit (outside _) pExt
    (by omega) size pairs z single

/-- Two real nontrivial blocks in the detached no-exception branch force
positive reserve in the original factor-critical component. -/
theorem positive_reserve_of_two_detached_blocks (Q : SimpleGraph X) (I : Set X)
    (ind : Q.IsIndepSet I) (largest : ∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (D : ℕ) (six : 6≤D) (par : Even D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (crit : PerfectAfterEveryDeletion Q)
    (N : (Q.induce Iᶜ).Subgraph) (hm : N.IsMatching) (max : N.edgeSet.ncard=matchingEdges (Q.induce Iᶜ))
    (gap : N.vertsᶜ.ncard+1=I.ncard) (noEx : exceptionalMateRegion (Q.induce Iᶜ) N=∅)
    (p q : ↥(N.vertsᶜ : Set ↥(Iᶜ : Set X))) (qp : q≠p)
    (bigP : 3≤(mateBlock (Q.induce Iᶜ) N p.val).ncard)
    (bigQ : 3≤(mateBlock (Q.induce Iᶜ) N q.val).ncard)
    (others : ∀j : ↥(N.vertsᶜ : Set ↥(Iᶜ : Set X)),j≠p → (Q.induce Iᶜ).IsClique (mateBlock (Q.induce Iᶜ) N j.val))
    (detached : ∀j : ↥(N.vertsᶜ : Set ↥(Iᶜ : Set X)),j≠p →
      ∀v∈mateBlock (Q.induce Iᶜ) N p.val∪zeroMateRegion (Q.induce Iᶜ) N,
      ∀u∈mateBlock (Q.induce Iᶜ) N j.val,¬(Q.induce Iᶜ).Adj v u) :
    1≤baseReserve Q D := by
  obtain ⟨s,hp,_,count⟩ := actual_detached_pair Q I ind largest D six par reg N hm max gap noEx p q qp bigP bigQ others detached
  apply detached_pair_positive_reserve Q I ind largest D six par reg crit s count
  rw [hp]
  apply block_with_zero_region_small _ N hm max p.val p.property
  intro T si
  have imageInd : Q.IsIndepSet (Subtype.val '' T) := by
    rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩ ne edge
    exact si hu hv (fun eq => ne (congrArg Subtype.val eq)) edge
  have cap := largest _ imageInd
  rwa [Set.ncard_image_of_injective _ Subtype.val_injective,←gap] at cap

#print axioms positive_reserve_of_two_detached_blocks
end JSP452Audit.StarHost
