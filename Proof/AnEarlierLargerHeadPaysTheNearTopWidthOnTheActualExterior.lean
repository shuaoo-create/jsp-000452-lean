import MoveAllInternalMatchingHolesToEitherOneOfTheTwoPalettes
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem typed_reduce_heads {A:Type*} (Y:SimpleGraph A) {a b x y w:ℕ} (rx:a≤x) (byh:b≤y)
    (seen:ExactTypedWidth Y x y w) : ExactTypedWidth Y a b w := by
  rcases seen with dead|⟨u,v,up,vp,eq,force⟩
  · exact Or.inl dead
  · exact Or.inr ⟨u,v,up,vp,eq,forces_uniform_subforests Y (fun _:Fin u => x) (fun _:Fin v => y) a b u v
      (by simp [rx]) (by simp [byh]) force⟩

theorem near_top_red_head_recovery {A B:Type u} [Finite A] [Finite B] (Y:SimpleGraph A) (C:SimpleGraph B) {s t r x y D j p:ℕ}
    (n:Fin s→ℕ) (m:Fin t→ℕ) (hs:0<s) (hn:Antitone n) (hm:Antitone m)
    (row:ForcingRow (Y⊕g C) s t (padDemand n) (padDemand m) r) (win:WinsHeight n m r j x y)
    (top:p<n ⟨0,hs⟩) (height:D=p+(y-1)) (pos:0<D) (cap:∀z,Nat.card (C.neighborSet z)≤D) :
    let M := Nat.card B/(x+1)
    let e := minimumExposure C D
    ExactTypedWidth Y x y (widthAt n m r j-M-e) := by
  intro M e
  obtain ⟨px,py,eq,rf,bg,span⟩ := win
  let z := n ⟨0,hs⟩
  have liveZ : 0<originalThresholdCount n z := (original_threshold_prefix n hn z ⟨0,hs⟩).1 le_rfl
  have xz : x≤z := (original_threshold_prefix n hn x ⟨0,hs⟩).2 rf
  obtain ⟨⟨R,rv,clear,holes⟩,⟨S,sv,_,zero⟩⟩ := near_top_actual_palettes C D p (y-1) z y pos height cap top (by omega)
  by_cases many:M<originalThresholdCount n x
  · have pack : UniformPackCap S x M := by
      intro n copy
      have cost := (genuine_uniform_pack_cap C x px) n (copy.mono_right sv)
      exact cost.trans (Nat.min_le_right _ _)
    have kept := palette_retains_typed_rectangle Y C S sv n m hn hm px py pack zero many bg row
    change ExactTypedWidth Y x y (originalThresholdCount n x+originalThresholdCount m y-1-r-M-0) at kept
    rw [span] at ⊢
    exact actual_typed_width_down Y kept (by omega)
  by_cases dead:widthAt n m r j≤M+e
  · exact Or.inl (by omega)
  have blue : e<originalThresholdCount m y := by omega
  have kept := palette_retains_typed_rectangle Y C R rv n m hn hm (show 0<z by omega) py clear holes liveZ blue row
  change ExactTypedWidth Y z y (originalThresholdCount n z+originalThresholdCount m y-1-r-0-e) at kept
  exact actual_typed_width_down Y (typed_reduce_heads Y xz le_rfl kept) (by omega)

theorem near_top_two_sided_recovery {A B:Type u} [Finite A] [Finite B] (Y:SimpleGraph A) (C:SimpleGraph B) {s t r x y D j:ℕ}
    (n:Fin s→ℕ) (m:Fin t→ℕ) (hs:0<s) (ht:0<t) (hn:Antitone n) (hm:Antitone m)
    (row:ForcingRow (Y⊕g C) s t (padDemand n) (padDemand m) r)
    (win:WinsHeight n m r j x y) (pos:0<D) (cap:∀z,Nat.card (C.neighborSet z)≤D)
    (large:(∃p,p<n ⟨0,hs⟩ ∧ D=p+(y-1)) ∨ (∃q,q<m ⟨0,ht⟩ ∧ D=q+(x-1))) :
    ExactTypedWidth Y x y (widthAt n m r j-Nat.card B/(min x y+1)-minimumExposure C D) := by
  rcases large with ⟨p,strict,sum⟩|⟨q,strict,sum⟩
  · have kept := near_top_red_head_recovery Y C n m hs hn hm row win strict sum pos cap
    have bound : Nat.card B/(x+1)≤Nat.card B/(min x y+1) := Nat.div_le_div_left (by omega) (by omega)
    exact actual_typed_width_down Y kept (by omega)
  · obtain ⟨px,py,eq,rf,bg,span⟩ := win
    have swap : widthAt m n r j=widthAt n m r j := by
      unfold widthAt offsetsAt
      rw [show rowCount t s r=rowCount s t r by simp only [rowCount,Nat.add_comm t s]]
      congr 1;apply Finset.filter_congr;intro k _
      rw [diagonal_swap m n]
    have cross : WinsHeight m n r j y x := ⟨py,px,by omega,bg,rf,by rw [swap,span,Nat.add_comm (originalThresholdCount n x)]⟩
    have kept := near_top_red_head_recovery Y C m n ht hm hn (swap_positive_forcing_row _ _ _ row) cross strict sum pos cap
    rw [swap] at kept
    have bound : Nat.card B/(y+1)≤Nat.card B/(min x y+1) := Nat.div_le_div_left (by omega) (by omega)
    exact actual_typed_width_down Y (exact_typed_width_swap Y kept) (by omega)

#print axioms typed_reduce_heads
#print axioms near_top_red_head_recovery
#print axioms near_top_two_sided_recovery
end JSP452Audit.StarHost
