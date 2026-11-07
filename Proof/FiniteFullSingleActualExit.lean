import SingleStrictLayerInventorySum
import FiniteFullSingleNumeric
import Mathlib.Tactic.ClearExcept
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem head_half_order_charge {s : ℕ} (hs:0<s) (n:Fin s→ℕ) :
    (n ⟨0,hs⟩-1)/2≤∑i,(n i-1)/2 := by
  exact Finset.single_le_sum (f:=fun i:Fin s => (n i-1)/2) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨0,hs⟩ : Fin s))

/-- Keep the matching rank and all positive uniform layers on the real
exterior. The actual strict mixed layer saves its two-prefix slack in
addition to the suppression savings on all higher layers. -/
theorem finite_full_single_exterior_exit {s t r D b : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (deg : 7≤D ∧ D≤14) (cap : ∀v,Nat.card (G.neighborSet v)≤D)
    (live : 0<rowCount s t r) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (head : n ⟨0,hs⟩=D) (opp : m ⟨0,ht⟩=b) (range : 2≤b ∧ 2*b≤D) (top : diagonal n m (r+2)=D+1)
    (d : ℕ) (rank : matchingEdges G+d=rowCount s t r) (strict : G.edgeSet.ncard<rowEnergy n m r)
    (data : BothActualSuccessors G K n m r (rowCount s t r) d (rowEnergy n m r))
    (esc : matchingEdges (G.induce K.core)<s) (inner : t+d+2*(∑j,(m j-1)/2)≤matchingEdges (G.induce K.core)+1)
    (endpoint : K.roots.ncard+r+2*(d+∑i,(n i-1)/2)≤t)
    (width : 1≤highestWidth n m r ∧ highestWidth n m r≤minimumExposure G D) (res : minimumExposure G D+1≤d)
    (root : D*minimumExposure G D+rootShortfall G K.roots D+2≤2*highestWidth n m r+2*(D/2)*(D/2+1))
    (nonunit : 0<originalThresholdCount ((componentBudget (G.induce K.core) n).entries n) 2)
    (trigger : FullMixedBoundary n m ht r D (matchingEdges (G.induce K.core))) : False := by
  let a := K.roots.ncard
  let H := G.induce K.core
  let μ := matchingEdges H
  let M := a+μ
  let ρ := minimumExposure G D
  let h := highestWidth n m r
  let C := widthAt n m r
  let f := originalThresholdCount n
  let B := originalThresholdCount m 2
  let W := componentBudget H n
  let A := f 2
  let c := originalThresholdCount (W.entries n) 2
  let V := μ+c-A
  let q := μ+1-t
  let X₀ := ∑i,(n i-1)/2
  let Y := ∑j,(m j-1)/2
  let R := G.induce K.rest
  let k := matchingEdges R
  let U := uniformEnvelope R
  change μ<s at esc;change t+d+2*Y≤μ+1 at inner
  change a+r+2*(d+X₀)≤t at endpoint
  change 1≤h ∧ h≤ρ at width;change ρ+1≤d at res
  have qeq : q+t=μ+1 := by dsimp [q];clear * - res inner;omega
  have sub : b<D := by clear * - deg range;omega
  have before : r<t := by clear * - endpoint res;omega
  have full : 0<f D := (original_threshold_prefix n hn D ⟨0,hs⟩).1 head.ge
  have px : 0<A := (original_threshold_prefix n hn 2 ⟨0,hs⟩).1 (by clear * - deg head;omega)
  have blue : 0<B := (original_threshold_prefix m hm 2 ⟨0,ht⟩).1 (by clear * - range opp;omega)
  have rect := actual_rectangle_le_column (r:=r) n m hn hm (a:=D) (b:=2) (h:=D+1) (by omega) full blue
  have peak := width_at_actual_top (r:=r) hs ht n m hn hm;rw [top] at peak;rw [peak] at rect
  change f D+B-1-r≤h at rect
  have budget : X₀+B≤t := by clear * - rect width full endpoint res;omega
  obtain ⟨_,fit,brow,_,_,_,_,_⟩ := data.1
  change W.loss≤μ at fit
  have len : s≤W.len+μ := by dsimp only [RemovalBudget.len];clear * - fit esc;omega
  have pos : 0<W.len := by dsimp only [RemovalBudget.len];clear * - fit esc;omega
  obtain ⟨fl,_,_,_⟩ := common_threshold_floors n hn pn W a μ 2 fit
  change A≤W.loss+c at fl
  have fitA : A≤μ+c := by clear * - fl fit;omega
  have bal : V+A=μ+c := by dsimp [V];clear * - fitA;omega
  let wB := widthAt (W.entries n) m (r+a)
  have env (j:ℕ) (jp:0<j) : wB j≤U j := widthAt_le_uniformEnvelope pos ht (W.entries n) m (W.entries_antitone n hn) hm
    (W.entries_positive n pn) pm _ _ j brow jp
  obtain ⟨two,actual,j,jlo,jhi,jb,mixed⟩ := full_retained_exterior_layers hs ht pos n m (W.entries n) hn hm
    (W.entries_antitone n hn) pn pm (W.entries_positive n pn) before live top (by clear * - deg;omega) fitA len nonunit blue px budget trigger
  change C 2≤M+wB 2 at two
  change ∀i,3≤ i → i≤D → C i≤f i+t-1-r ∨ C i≤M+wB i at actual
  change C j+V≤M+wB j at mixed
  rw [opp] at jb
  obtain ⟨T,p7,p8,p9,supp⟩ := single_exact_suppression_floor G K n m hs hn hm pm (by clear * - deg;omega) cap head row
  let η := T.ncard
  let K₀ := max (a+q+r) (μ+1-η)
  have axis (i:ℕ) (ip:0< i) (id:i≤D) (pure:C i≤f i+t-1-r) : C i+K₀≤M+U i+f i :=
    single_suppression_axis a μ t r η (f i) (C i) (U i) q before qeq pure (supp i ip id)
  have inside (i:ℕ) (il:3≤ i) (ih:i≤b+1) : C i≤M+U i+f i := by
    have id : i≤D := by clear * - ih sub;omega
    rcases actual i il id with pure|cheap
    · have bound := axis i (by omega) id pure;omega
    · have bound := env i (by omega);omega
  have upper (i:ℕ) (il:b+2≤ i) (ih:i≤D) : C i+K₀≤M+U i+f i :=
    axis i (by omega) ih (full_upper_pure_only hs ht n m hn hm pn pm opp top live range.1 budget i il ih)
  have low := two.trans (Nat.add_le_add_left (env 2 (by decide)) M)
  have save := mixed.trans (Nat.add_le_add_left (env j (by omega)) M)
  have account := single_strict_layer_sum D b M K₀ V j C U f range.1 sub jlo jb low inside save upper
  have volume := nonunit_slot_volume G K n hn
  change 3*A≤3*c+2*μ+a+ρ at volume
  have slot := original_two_threshold_slot_guard G K n hn (by clear * - deg;omega) cap
  change D*ρ+rootShortfall G K.roots D+D*A≤D*(μ+c) at slot
  rw [←bal,Nat.mul_add] at slot
  have sslot : D*ρ+rootShortfall G K.roots D≤D*V := by omega
  have vx := head_half_order_charge hs n
  have vy := head_half_order_charge ht m
  rw [head] at vx;rw [opp] at vy
  have numeric := finite_full_single_numerical D b μ a r d h ρ X₀ Y t q η V K₀ (rootShortfall G K.roots D)
    deg range width res qeq (by clear * - qeq inner;omega) endpoint vx vy (by clear * - volume bal;omega) sslot
    (Nat.sub_le _ _) root p7 p8 p9 (le_max_left _ _) (by have := le_max_right (a+q+r) (μ+1-η);dsimp [K₀];omega)
  have mass := large_threshold_sum n (D-2)
  change (∑z∈Finset.range (D-2),f (z+3))≤2*X₀ at mass
  have paid := (envelope_reserve_account R (D-1)).1
  change envelopeReserve R (D-1)+(k+∑z∈Finset.range (D-1),U (z+2))=R.edgeSet.ncard at paid
  have split := region_rank_partition G K.barrier K.tight K.pieces
  change matchingEdges G=M+k at split
  have area := original_area_by_height hs ht n m hn hm pn pm top (by clear * - deg;omega)
  change rowEnergy n m r=rowCount s t r+(∑z∈Finset.range (D-1),C (z+2))+h at area
  have edge := ordinary_region_original_edge_account G D cap K
  change 2*G.edgeSet.ncard+rootShortfall G K.roots D=2*D*M+D*ρ+crossCount G K.roots K.rest+2*R.edgeSet.ncard at edge
  have prod : (D-1)*M+M=D*M := by
    conv_rhs => rw [show D=D-1+1 by clear * - deg;omega,Nat.add_mul,Nat.one_mul]
  clear * - rank split mass paid area edge prod account numeric strict
  nlinarith only [rank,split,mass,paid,area,edge,prod,account,numeric,strict,Nat.zero_le (crossCount G K.roots K.rest),
    Nat.zero_le (envelopeReserve R (D-1))]

#print axioms head_half_order_charge
#print axioms finite_full_single_exterior_exit
end JSP452Audit.StarHost