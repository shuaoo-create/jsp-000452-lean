import SixOmitTheMixedThreshold
namespace JSP452Audit.StarHost
open SimpleGraph

theorem six_suppression_floor {s t r : ℕ} {X : Type*} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G 6)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (hn : Antitone n) (hm : Antitone m)
    (pm : ∀j,1≤m j) (cap : ∀x,Nat.card (G.neighborSet x)≤6) (head : n ⟨0,hs⟩=6)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    let H := G.induce K.core
    let size := 2*matchingEdges H+K.roots.ncard+minimumExposure G 6
    ∃T:Set K.core,5*T.ncard≤2*size ∧
      ∀j,0<j → j≤6 → t-(r+K.roots.ncard+T.ncard)≤uniformEnvelope (G.induce K.rest) j := by
  intro H size
  obtain ⟨T,cover,fee⟩ := quarter_full_core_set H 6
  have inside (x:K.core) : Nat.card (H.neighborSet x)≤6 := (induced_neighbor_count_le G K.core x).trans (cap _)
  obtain ⟨R,sub,small,light⟩ := dominated_full_red_split H 6 (by decide) inside T cover
  have order : Nat.card ↥K.core=size := (Nat.card_coe_set_eq _).trans K.core_order
  rw [order] at fee;norm_num at fee
  have bound : 5*T.ncard≤2*size := by
    exact_mod_cast (show (5:ℚ)*T.ncard≤2*size by linarith only [fee,Nat.cast_nonneg size (α:=ℚ)])
  exact ⟨T,bound,suppressed_core_exterior_floor G K R sub small T.ncard light n m hs hn hm pm head (by decide) row⟩

#print axioms six_suppression_floor
end JSP452Audit.StarHost