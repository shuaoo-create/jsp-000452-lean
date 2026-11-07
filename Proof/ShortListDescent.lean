import FinalDescentLengths
import UnpaidDensityObstruction
import FlexibleComponents

namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- A strict source with an actual two-component shorter target can occur
only on its initial row. Its matching deficit and edge shortfall are both one. -/
theorem two_list_strict_profile (F : StrictFamily.{u}) (two : min F.s F.t=2) :
    F.r=0 ∧ F.rank=matchingEdges F.G+1 ∧ matchingEdges F.G=max F.s F.t ∧
      F.G.edgeSet.ncard+1=rowEnergy F.n F.m F.r := by
  obtain ⟨lengths,lower⟩ := strict_source_strong_lengths F
  rw [two] at lengths
  have budget := row_energy_budget F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.row
  have strict := F.strict
  change rowEnergy F.n F.m F.r + matchingEdges F.G ≤ F.G.edgeSet.ncard+F.rank at budget
  have defic : matchingEdges F.G<F.rank := by omega
  have zero : F.r=0 := by omega
  have one : F.rank=matchingEdges F.G+1 := by omega
  have shape : F.rank=max F.s F.t+1 := by
    dsimp [StrictFamily.rank,rowCount]
    omega
  omega

/-- When the envelope is zero, every exposed component has reserve zero,
contributes exactly one unit of exposure, and uses at least D+4 covered
vertices. All component accounts are on the original host. -/
theorem zero_envelope_exposure_rank_charge {X : Type*} [Finite X] (G : SimpleGraph X)
    (D k : ℕ) (large : 3≤D) (cap : ∀v,Nat.card (G.neighborSet v)≤D)
    (zero : envelopeReserve G k=0) :
    (D+4)*minimumExposure G D≤2*matchingEdges G := by
  classical
  let _ := Fintype.ofFinite G.ConnectedComponent
  have budget := envelopeReserve_component_sum_le G k
  have localCharge (c : G.ConnectedComponent) :
      (D+4)*minimumExposure c.toSimpleGraph D ≤ 2*matchingEdges c.toSimpleGraph := by
    by_cases free : minimumExposure c.toSimpleGraph D=0
    · simp [free]
    have oneTerm := Finset.single_le_sum (s:=Finset.univ)
      (f:=fun c : G.ConnectedComponent => envelopeReserve c.toSimpleGraph k)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    have unpaid : envelopeReserve c.toSimpleGraph k<minimumExposure c.toSimpleGraph D := by
      have zeroHere := oneTerm.trans budget
      omega
    obtain ⟨reg,crit,_,_,_⟩ := unpaid_component_obstruction G D k large cap c unpaid
    let v : c.supp := c.nonempty_supp.to_subtype.some
    have exposure := regular_factorCritical_exposure c.toSimpleGraph crit v D
      (fun x => (component_degree_eq G c x).trans (reg x))
    have order := factorCritical_order_rank c.toSimpleGraph crit v
    have size := (unpaid_component_density_obstruction G D k large cap c unpaid).1
    change Nat.card c.supp=2*matchingEdges c.toSimpleGraph+1 at order
    change D+5≤Nat.card c.supp at size
    rw [exposure,Nat.mul_one]
    omega
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun c _ => localCharge c)
  rw [←Finset.mul_sum,←Finset.mul_sum,←minimumExposure_component_total,
    ←(component_rank_budget_gluing G).1] at sum
  exact sum

/-- Failure keeps the given lists through normalization, because their shorter
length forces the deletion index back to zero. It requires an even head cap
of at least four and enough original rank for every top-column exposure. -/
theorem two_list_failure_width_obstruction {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (two : min s t=2)
    (fail : sizeRamsey (forest n) (forest m)≠∑ k∈Finset.Icc 2 (s+t),diagonal n m k) :
    let D := diagonal n m 2-1
    Even D ∧ 4≤D ∧ 1≤highestWidth n m 0 ∧
      (D+4)*highestWidth n m 0≤2*max s t := by
  intro D
  obtain ⟨V,G,U,row,rank,sr,tr,edges,under,cap,_,heads⟩ :=
    normalized_source_of_failure hs ht n m hn hm pn pm fail
  let Y := G.induce {x | x∉U}
  have initial : U.card=0 := by omega
  rw [initial] at row rank edges under cap heads
  change ForcingRow Y s t (padDemand n) (padDemand m) 0 at row
  change Y.edgeSet.ncard+1=rowEnergy n m 0 at edges
  change ∀x,Nat.card (Y.neighborSet x)≤D at cap
  have strict : Y.edgeSet.ncard<rowEnergy n m 0 := by omega
  have count : rowCount s t 0=max s t+1 := by dsimp [rowCount]; omega
  have lower := row_suffix_matching_floor n m pn pm Y row 0 0 hs ht rfl
  simp only [Nat.sub_zero] at lower
  change matchingEdges Y<rowCount s t 0 at under
  have matching : matchingEdges Y=max s t := by omega
  obtain ⟨i,j,index,peak⟩ := diagonal_attained n m hs ht 0 (by omega)
  have atPeak := heads i j index peak
  change diagonal n m 2=n i+m j-1 at peak
  have large : 3≤D := by
    by_contra! small
    have top : diagonal n m 2≤3 := by dsimp [D] at small; omega
    have red : ∀k,n k≤2 := by
      intro k
      have le : n k≤n i := hn (show i≤k by change i.val≤k.val; omega)
      omega
    have blue : ∀k,m k≤2 := by
      intro k
      have le : m k≤m j := hm (show j≤k by change j.val≤k.val; omega)
      omega
    exact fail (all_binary_sizeRamsey hs ht n m hn hm pn pm red blue)
  have height : diagonal n m 2≤D+1 := by dsimp [D]; omega
  have env := row_envelope_reserve hs ht n m hn hm pn pm Y 0 D row height
  have zero : envelopeReserve Y D=0 := by omega
  obtain ⟨first,priced⟩ := row_minimum_exposure hs ht n m hn hm pn pm Y 0 (by omega) row cap
  change highestWidth n m 0≤minimumExposure Y D at priced
  have unpaid : envelopeReserve Y D<minimumExposure Y D := by omega
  obtain ⟨c,miss⟩ := exists_unpaid_original_component Y D D unpaid
  obtain ⟨_,_,even,four,_⟩ := unpaid_component_obstruction Y D D large cap c miss
  have charge := zero_envelope_exposure_rank_charge Y D D large cap zero
  rw [matching] at charge
  exact ⟨even,four,first,(Nat.mul_le_mul_left (D+4) priced).trans charge⟩

/-- The complete original formula for two-component shorter lists whenever
the top degree is odd, or the top-column charge exceeds the longer length's
available matching endpoints. -/
theorem erdos561_two_list_by_width {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (two : min s t=2)
    (excluded : Odd (diagonal n m 2-1) ∨
      2*max s t < (diagonal n m 2-1+4)*highestWidth n m 0) :
    sizeRamsey (forest n) (forest m)=∑ k∈Finset.Icc 2 (s+t),diagonal n m k := by
  by_contra fail
  obtain ⟨even,_,_,budget⟩ := two_list_failure_width_obstruction hs ht n m hn hm pn pm two fail
  rcases excluded with odd|tooMuch
  · exact (Nat.not_even_iff_odd.mpr odd) even
  · exact tooMuch.not_ge budget

/-- Two stars against two or three stars, in either order, have the full
original size Ramsey formula for arbitrary positive nonincreasing sizes. -/
theorem erdos561_two_by_at_most_three {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (two : min s t=2) (short : max s t≤3) :
    sizeRamsey (forest n) (forest m)=∑ k∈Finset.Icc 2 (s+t),diagonal n m k := by
  by_contra fail
  obtain ⟨_,four,positive,budget⟩ := two_list_failure_width_obstruction hs ht n m hn hm pn pm two fail
  have lower := Nat.mul_le_mul_left (diagonal n m 2-1+4) positive
  rw [Nat.mul_one] at lower
  omega

/-- A constant initial segment in either original list contributes that many
distinct offsets at the actual first diagonal height. -/
theorem initial_run_le_highest_width {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (l : ℕ) (run : (l≤s ∧ ∀i:Fin s,i.val<l → n i=n ⟨0,hs⟩) ∨
      (l≤t ∧ ∀j:Fin t,j.val<l → m j=m ⟨0,ht⟩)) :
    l≤highestWidth n m 0 := by
  have first : diagonal n m 2=n ⟨0,hs⟩+m ⟨0,ht⟩-1 := by
    obtain ⟨i,j,index,eq⟩ := diagonal_attained n m hs ht 0 (by omega)
    have sameI : i=⟨0,hs⟩ := Fin.ext (by change i.val=0; omega)
    have sameJ : j=⟨0,ht⟩ := Fin.ext (by change j.val=0; omega)
    simpa only [sameI,sameJ,Nat.zero_add] using eq
  have sub : Finset.range l ⊆ highestOffsets n m 0 := by
    intro k hk
    have within := Finset.mem_range.mp hk
    have live : k<s+t-1 := by rcases run with h|h <;> omega
    have pair : ∃(i : Fin s)(j : Fin t), i.val+j.val=k ∧ n i=n ⟨0,hs⟩ ∧ m j=m ⟨0,ht⟩ := by
      rcases run with h|h
      · exact ⟨⟨k,by omega⟩,⟨0,ht⟩,by simp,h.2 _ within,rfl⟩
      · exact ⟨⟨0,hs⟩,⟨k,by omega⟩,by simp,rfl,h.2 _ within⟩
    obtain ⟨i,j,idx,eqN,eqM⟩ := pair
    have att := antiDiag_member n m i j
    rw [idx,eqN,eqM,←first] at att
    have upper := earlier_diagonal_dominates hs ht n m hn hm (i:=0) (j:=k) (by omega) live
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by dsimp [rowCount]; omega),
      by simpa only [Nat.zero_add] using le_antisymm upper att⟩
  simpa only [Finset.card_range,highestWidth] using Finset.card_le_card sub

/-- For a shorter list of length two, a run of equal largest stars on either
side longer than a quarter of the longer list rules out every strict host. -/
theorem erdos561_two_list_by_head_run {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (two : min s t=2)
    (l : ℕ) (long : max s t<4*l) (run :
      (l≤s ∧ ∀i:Fin s,i.val<l → n i=n ⟨0,hs⟩) ∨
      (l≤t ∧ ∀j:Fin t,j.val<l → m j=m ⟨0,ht⟩)) :
    sizeRamsey (forest n) (forest m)=∑ k∈Finset.Icc 2 (s+t),diagonal n m k := by
  by_contra fail
  obtain ⟨_,four,_,budget⟩ := two_list_failure_width_obstruction hs ht n m hn hm pn pm two fail
  have width := initial_run_le_highest_width hs ht n m hn hm l run
  have floor := Nat.mul_le_mul_right (highestWidth n m 0) (show 8≤diagonal n m 2-1+4 by omega)
  omega

/-- In particular any two arbitrary stars against any positive number t≥2
of equal-size positive stars have the complete original formula. -/
theorem erdos561_two_against_uniform {t : ℕ} (ht : 2≤t)
    (n : Fin 2 → ℕ) (hn : Antitone n) (pn : ∀i,1≤n i) (b : ℕ) (pb : 0<b) :
    sizeRamsey (forest n) (forest (fun _ : Fin t => b))=
      ∑ k∈Finset.Icc 2 (2+t),diagonal n (fun _ : Fin t => b) k := by
  exact erdos561_two_list_by_head_run (s:=2) (t:=t) (by decide) (by omega)
    n (fun _ : Fin t => b) hn (fun _ _ _ => le_rfl) pn (fun _ => pb) (by omega) t
    (by omega) (Or.inr ⟨le_rfl,fun _ _ => rfl⟩)

#print axioms initial_run_le_highest_width
#print axioms erdos561_two_list_by_head_run
#print axioms erdos561_two_against_uniform
#print axioms two_list_strict_profile
#print axioms zero_envelope_exposure_rank_charge
#print axioms two_list_failure_width_obstruction
#print axioms erdos561_two_list_by_width
#print axioms erdos561_two_by_at_most_three
end JSP452Audit.StarHost

