import ActualFullDegreeCoreSuppression
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- One actual set and coloring of the original core supplies a common
floor on both physical inventories for every height through D. -/
theorem actual_full_suppression_floor {s t r D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (hn : Antitone n) (hm : Antitone m)
    (pm : ∀j,1≤m j) (deg : 9≤D) (cap : ∀x,Nat.card (G.neighborSet x)≤D) (head : n ⟨0,hs⟩=D)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    let H := G.induce K.core
    let μ := matchingEdges H
    let a := K.roots.ncard
    let ρ := minimumExposure G D
    ∃T:Set K.core,13*T.ncard≤4*(2*μ+a+ρ) ∧
      (∀v,Nat.card (H.neighborSet v)=D → v∈T ∨ ∃w∈T,H.Adj v w) ∧
      (∀j,0<j → j≤D → t-(r+a+T.ncard)≤uniformEnvelope (G.induce K.rest) j ∧
        t-(r+a+T.ncard)≤uniformEnvelope (eraseInternal G K.core) j) := by
  intro H μ a ρ
  obtain ⟨T,cover,fee⟩ := quarter_core_integer_price H D deg
  have inside (x:K.core) : Nat.card (H.neighborSet x)≤D := (induced_neighbor_count_le G K.core x).trans (cap _)
  obtain ⟨R,sub,small,light⟩ := dominated_full_red_split H D (by omega) inside T cover
  have floor := suppressed_core_exterior_floor G K R sub small T.ncard light n m hs hn hm pm head (by omega) row
  have size := K.core_order
  change K.core.ncard=2*μ+a+ρ at size
  rw [Nat.card_coe_set_eq,size] at fee
  refine ⟨T,fee,cover,?_⟩
  intro j p b
  have cheap := floor j p b
  exact ⟨cheap,cheap.trans (exterior_envelope_in_erased G K j)⟩

theorem strict_actual_suppression_floor (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let μ := matchingEdges (F.G.induce K.core)
    let a := K.roots.ncard
    let ρ := minimumExposure F.G D
    9≤D → (F.n ⟨0,F.hs⟩=D → ∃T:Set K.core,13*T.ncard≤4*(2*μ+a+ρ) ∧
      ∀j,0<j → j≤D → F.t-(F.r+a+T.ncard)≤uniformEnvelope (F.G.induce K.rest) j ∧
        F.t-(F.r+a+T.ncard)≤uniformEnvelope (eraseInternal F.G K.core) j) ∧
      (F.m ⟨0,F.ht⟩=D → ∃T:Set K.core,13*T.ncard≤4*(2*μ+a+ρ) ∧
      ∀j,0<j → j≤D → F.s-(F.r+a+T.ncard)≤uniformEnvelope (F.G.induce K.rest) j ∧
        F.s-(F.r+a+T.ncard)≤uniformEnvelope (eraseInternal F.G K.core) j) := by
  intro D μ a ρ deg
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  constructor
  · intro red
    obtain ⟨T,fee,_,floor⟩ := actual_full_suppression_floor F.G K F.n F.m F.hs F.hn F.hm F.pm deg cap red F.row
    exact ⟨T,fee,floor⟩
  · intro blue
    obtain ⟨T,fee,_,floor⟩ := actual_full_suppression_floor F.G K F.m F.n F.ht F.hm F.hn F.pn deg cap blue
      (swap_positive_forcing_row F.G _ _ F.row)
    exact ⟨T,fee,floor⟩

#print axioms actual_full_suppression_floor
#print axioms strict_actual_suppression_floor
end JSP452Audit.StarHost