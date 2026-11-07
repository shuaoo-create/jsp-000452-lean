import PairProfileAtLargeSize
import SingleOwnerFromFour
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] [Nonempty X]

theorem pair_at_large_size_positive_from_four (Q : SimpleGraph X) (I : Set X) (ind : Q.IsIndepSet I)
    (largest : ∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (D : ℕ) (four : 4≤D) (par : Even D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (crit : PerfectAfterEveryDeletion Q) (s : DetachedMatePair (Q.induce Iᶜ))
    (count : s.singles.ncard+3=I.ncard)
    (size : (Subtype.val '' s.preferred).ncard=D+1)
    (cost : crossCount Q (Subtype.val '' s.preferred) (Subtype.val '' s.preferred)ᶜ=D+2)
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
  obtain ⟨critical,⟨z,_,single⟩⟩ := detached_pair_profile_at_large_size Q I ind largest D four par reg s size cost small
  change P.ncard=D+1 at size
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
  exact single_root_profile_impossible_from_four Q I P D four par reg crit (outside _) pExt
    (by omega) size pairs z single

#print axioms pair_at_large_size_positive_from_four
end JSP452Audit.StarHost
