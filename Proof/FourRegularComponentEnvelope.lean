import FivePointPairReserve
import TwinTrianglesPositiveReserve
import FourResidualAlternative
import FourNontrivialBlock
import ExceptionalPartitionPays
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] [Nonempty X]

theorem four_connected_detached_pair_pays (Q : SimpleGraph X) (I : Set X)
    (ind : Q.IsIndepSet I) (largest : ∀A:Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (conn : Q.Connected) (reg : ∀v,Nat.card (Q.neighborSet v)=4) (crit : PerfectAfterEveryDeletion Q)
    (s : DetachedMatePair (Q.induce Iᶜ)) (count : s.singles.ncard+3=I.ncard)
    (small : NoIndependentTriple ((Q.induce Iᶜ).induce s.preferred)) : 1≤baseReserve Q 4 := by
  obtain ⟨c3,_,p6,hp⟩ := four_detached_pair_exact_prices Q I ind largest reg s count
  rcases hp with five|⟨p3,cl⟩
  · exact pair_at_large_size_positive_from_four Q I ind largest 4 (by decide) (by decide) reg crit s count five p6 small
  obtain ⟨h,_,_⟩ := original_twin_triangles Q I s count p3 c3 cl
  exact twin_triangles_positive_reserve Q I h ind reg conn crit

/-- Every four-regular connected factor-critical host pays the envelope on its
actual labels, including real exceptional and nonexceptional partitions. -/
theorem four_regular_component_envelope (Q : SimpleGraph X) (k : ℕ) (conn : Q.Connected)
    (reg : ∀v,Nat.card (Q.neighborSet v)=4) (crit : PerfectAfterEveryDeletion Q) :
    minimumExposure Q 4≤envelopeReserve Q k := by
  by_contra! fail
  obtain ⟨I,v,M,ind,largest,three,_,_,_,_,hm,max,_,labels,count,_,anti,_⟩ :=
    unpaid_regular_mate_decomposition Q 4 k (by decide) reg crit fail
  let H := Q.induce Iᶜ
  let N := restrictedOutsideMatching Q I M
  have exp := regular_factorCritical_exposure Q crit v 4 reg
  have env := (envelope_reserve_account Q 4).2
  have trunc := envelopeReserve_le_truncation Q 4 k (fun u => (reg u).le)
  have zero : baseReserve Q 4=0 := by omega
  have gap : N.vertsᶜ.ncard+1=I.ncard := by
    rwa [←labels,Set.ncard_image_of_injective _ Subtype.val_injective] at count
  have antiH := pullback_mate_antineighborhood_clique Q I N _ labels anti
  by_cases noEx : exceptionalMateRegion H N=∅
  · have cl := antiH.subset (zeroMateRegion_subset_anti H N)
    have big := four_zero_reserve_has_nontrivial_block Q I conn ind largest three reg crit zero N hm max gap noEx cl
    obtain ⟨w,hw,large,joined,others⟩ :=
      exists_preferred_connected_block Q I ind largest 4 (by decide) reg N hm max gap noEx cl big
    have alt := reserve_or_two_detached_parts_from_four Q I ind largest three 4 (by decide) (by decide)
      reg crit N hm max gap noEx ⟨w,hw⟩ large joined
      (fun j ne => others j.val j.property (fun e => ne (Subtype.ext e)))
    rcases alt with paid|⟨q,s,_,part,_,n⟩
    · omega
    have small : NoIndependentTriple (H.induce s.preferred) := by
      rw [part]
      apply block_with_zero_region_small H N hm max w hw
      intro T si
      have imageInd : Q.IsIndepSet (Subtype.val '' T) := by
        rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ ne e
        exact si ha hb (fun eq => ne (congrArg Subtype.val eq)) e
      have cap := largest _ imageInd
      rwa [Set.ncard_image_of_injective _ Subtype.val_injective,←gap] at cap
    have paid := four_connected_detached_pair_pays Q I ind largest conn reg crit s n small
    omega
  have paid := exceptional_partition_positive Q I ind largest 4 (by decide) (by decide) reg crit N hm max gap antiH noEx
  omega

#print axioms four_connected_detached_pair_pays
#print axioms four_regular_component_envelope
end JSP452Audit.StarHost
