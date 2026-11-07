import TenDegreeOriginalCertificateAlternatives
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

structure TenOuterCut {X:Type u} [Finite X] (G:SimpleGraph X) where
  S : Set X
  T : Set X
  apart : Disjoint S T
  imbalance : S.ncard=T.ncard+1
  score : ℕ
  positive : 1≤score
  small : score≤2
  actual : originalFactorCut G 3 7 S T=(score:ℤ)

namespace TenOuterCut
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenOuterCut G)
abbrev roots := K.S∪K.T
noncomputable def pieces := uniformOddPieces G 3 7 K.S K.T
noncomputable def core := regionCore G K.roots K.pieces
noncomputable def support := K.roots∪K.core
noncomputable def port (C:↥K.pieces) := crossCount G (cutPieceSet G K.roots C.val) K.roots
noncomputable def excessPairs : ℕ := by
  classical
  let _ := Fintype.ofFinite K.pieces
  exact ∑C:↥K.pieces,(K.port C-2)/2
noncomputable def rootDefect (_K:TenOuterCut G) (A:Set X) := 10*A.ncard-originalDegreeSum G A

theorem core_outside : K.core⊆K.rootsᶜ := by
  rintro _ ⟨v,rfl,_⟩
  exact v.property

theorem port_size (cap:∀v,Nat.card (G.neighborSet v)≤10) (none:(oddRegularComponents G 10).ncard=0)
    (C:↥K.pieces) : 2≤K.port C ∧ 2∣K.port C := by
  have div := cut_piece_boundary_parity G K.roots C.val 5
    (fun x hx => uniform_tight_piece_full G 3 7 cap K.S K.T C.val C.property x hx)
  change 2∣K.port C at div
  have count := portless_uniform_count G 3 7 cap K.S K.T
  change (portlessUniformPieces G 3 7 K.S K.T).ncard≤(oddRegularComponents G 10).ncard at count
  have positive : K.port C≠0 := by
    intro zero
    have mem : C.val∈portlessUniformPieces G 3 7 K.S K.T := ⟨C.property,zero⟩
    have pos := (Set.ncard_pos (Set.toFinite _)).mpr (show (portlessUniformPieces G 3 7 K.S K.T).Nonempty from ⟨_,mem⟩)
    omega
  exact ⟨by omega,div⟩

theorem total_ports (cap:∀v,Nat.card (G.neighborSet v)≤10) (none:(oddRegularComponents G 10).ncard=0) :
    crossCount G K.core K.roots=2*K.pieces.ncard+2*K.excessPairs := by
  classical
  let _ := Fintype.ofFinite K.pieces
  have each (C:↥K.pieces) : K.port C=2+2*((K.port C-2)/2) := by
    obtain ⟨_,_⟩ := K.port_size cap none C
    omega
  change crossCount G (regionCore G K.roots K.pieces) K.roots=_
  rw [selected_cut_cross_sum G K.roots K.pieces K.roots]
  change (∑C:↥K.pieces,K.port C)=2*K.pieces.ncard+2*(∑C:↥K.pieces,(K.port C-2)/2)
  calc
    _ = ∑C:↥K.pieces,(2+2*((K.port C-2)/2)) := Finset.sum_congr rfl (fun C _ => each C)
    _ = _ := by rw [Finset.sum_add_distrib,Finset.mul_sum];simp [←Nat.card_eq_fintype_card,Nat.mul_comm]
end TenOuterCut

theorem strict_ten_cut_when_no_odd_component (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (none:(oddRegularComponents F.G 10).ncard=0) :
    ∃K:TenOuterCut F.G,highestWidth F.n F.m F.r≤K.score ∧ K.score+2≤minimumExposure F.G 10 := by
  have hp := (strict_ten_inventory F paid ten).1
  obtain ⟨_,_,_,_,S,T,dis,imbal,fee,small,endpt,_⟩ := strict_ten_excess_width_cut F paid ten (by omega)
  let z := originalFactorCut F.G 3 7 S T
  have eq : (z.toNat:ℤ)=z := Int.toNat_of_nonneg (by change 0≤originalFactorCut F.G 3 7 S T;omega)
  have cap (v:F.X) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq ten
  have top := (three_prices_of_ten_cut F.G cap S T dis).2.2.1
  change _=z+2 at endpt
  change _≤(minimumExposure F.G 10:ℤ) at top
  change (highestWidth F.n F.m F.r:ℤ)≤z at fee
  change z≤2 at small
  exact ⟨⟨S,T,dis,imbal,z.toNat,by omega,by omega,eq.symm⟩,by change _≤z.toNat;omega,by change z.toNat+2≤_;omega⟩

#print axioms TenOuterCut.port_size
#print axioms TenOuterCut.total_ports
#print axioms strict_ten_cut_when_no_odd_component
end JSP452Audit.StarHost
