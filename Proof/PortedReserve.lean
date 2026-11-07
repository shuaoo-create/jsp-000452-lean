import GoodAndBadMatching
import SameLabelPortRepair
import UnitedPortIndependent
import ExtendRepairedCut
import EvenGoodRegionSaving
import OddDegreeReserve
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]
/-- Complete even-degree ported cut on the original graph. The good
region and the bad-port witnesses share the identical matching and labels. -/
theorem even_ported_independent_cut (G : SimpleGraph X) (D : ℕ) (large : 2≤D) (even : Even D)
    (cap : ∀x,Nat.card (G.neighborSet x)≤D) (noReg : NoOriginalRegularCritical G D) :
    ∃ I : Set X,G.IsIndepSet I ∧ (∀x∈I,Nat.card (G.neighborSet x)=D) ∧
      deletionBudget (G.induce Iᶜ) D=0 ∧
      baseReserve (G.induce Iᶜ) D+minimumExposure G D≤baseReserve G D := by
  classical
  have pos : 0<D := by omega
  obtain ⟨S,A,T,tight,data,inside,opt,balance,⟨plan⟩⟩ := exists_optimized_disjoint_ports G D pos cap
  let h := (goodFullClass G S D\Set.range A.place).ncard
  have split := large_good_piece_split G S D cap noReg (fun c => (data c).2) T inside
  obtain ⟨M,pick,hm,max,_,_,image,roots,ports,goodFree⟩ :=
    good_and_bad_port_matching G S tight data D A opt plan T inside split
  choose y z low ay ne oldYZ exposed notAdj different using ports
  let cf := chosenComponents plan
  let I0 := augmentedPortLabels G S D A pick cf plan.root (fun i => pick (A.place (plan.root i))) z
  let P := goodPortSet G S D T (largeGoodPieces G S D T) pick
  obtain ⟨ind0,full0,size,rank,zero⟩ := base_port_repair_on_labels G S tight data D pos cap A opt plan M hm max
    pick image roots y z ay oldYZ notAdj different
  obtain ⟨ind,full,includes,_⟩ := united_port_independent G S D A T inside pick cf plan.root z
    (fun i => i.val.property) cap (fun i => M.adj_sub (roots (plan.root i)))
    (fun c free hc => goodFree c hc free.1) split ind0 full0
  have saving := even_good_region_saving G S D large even cap noReg data T inside pick h balance (I0∪P) includes
  have enough := plan.enough
  have pay := extended_repaired_cut_pays G D large I0 P plan.chosen.ncard h zero rank size ind full
    (by dsimp [h] at *; omega) saving
  have zclear := (extend_repaired_cut G D I0 P (minimumExposure G D) plan.chosen.ncard zero rank size).1
  exact ⟨I0∪P,ind,full,zclear,pay⟩

/-- Full ported reserve for every positive degree bound; graphs whose
original components are regular and factor-critical are handled separately. -/
theorem ported_reserve (G : SimpleGraph X) (D k : ℕ) (pos : 0<D)
    (cap : ∀x,Nat.card (G.neighborSet x)≤D) (noReg : NoOriginalRegularCritical G D) :
    minimumExposure G D ≤ baseReserve G k ∧ minimumExposure G D ≤ envelopeReserve G k := by
  by_cases odd : Odd D
  · exact odd_degree_reserve G D k odd cap
  have parity := Nat.odd_iff.not.mp odd
  have even : Even D := Nat.even_iff.mpr (by omega)
  obtain ⟨I,_,_,_,pay⟩ := even_ported_independent_cut G D (by omega) even cap noReg
  have stable := baseReserve_le_truncation G D k cap
  have envelope := (envelope_reserve_account G k).2
  omega
#print axioms even_ported_independent_cut
#print axioms ported_reserve
end JSP452Audit.StarHost
