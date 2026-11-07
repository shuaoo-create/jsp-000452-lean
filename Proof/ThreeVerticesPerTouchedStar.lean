import ActualSevenPieceSuccessor
namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded

theorem three_vertices_per_touched_star {I X:Type*} [Finite I] [Finite X] (G R P:SimpleGraph X)
    (U:Set X) (subR:R≤G) (subP:P≤G) (inside:∀⦃x y⦄,P.Adj x y → x∈U) (a:ℕ) (two:2≤a)
    (f:(forest (fun _:I => a)).Copy (R⊔P)) :
    3*(touchedStars R P (fun _:I => a) f).ncard≤U.ncard+crossCount G U Uᶜ := by
  classical
  let n := fun _:I => a
  let B := touchedStars R P n f
  let V := {p:↥U×↥(Uᶜ:Set X) // G.Adj p.1.val p.2.val}
  let idx : Fin 3↪Fin (a+1) := Fin.castLEEmb (by omega)
  let val (s:↥B×Fin 3) : X := f ⟨s.1.val,idx s.2⟩
  have centerIn (i:↥B) : f (center n i.val)∈U := by
    obtain ⟨j,miss⟩ := i.property
    exact inside ((f.toHom.map_adj (starEdge n ⟨i.val,j⟩)).resolve_left miss)
  have outside (s:↥B×Fin 3) (out:val s∉U) : G.Adj (f (center n s.1.val)) (val s) := by
    have atIndex (j:Fin (a+1)) : f ⟨s.1.val,j⟩∉U → G.Adj (f (center n s.1.val)) (f ⟨s.1.val,j⟩) := by
      refine Fin.cases (fun h => (h (centerIn s.1)).elim) (fun j _ => ?_) j
      exact (sup_le subR subP) (f.toHom.map_adj (starEdge n ⟨s.1.val,j⟩))
    exact atIndex (idx s.2) out
  let send (s:↥B×Fin 3) : ↥U⊕V := if h:val s∈U then .inl ⟨val s,h⟩ else
    .inr ⟨(⟨f (center n s.1.val),centerIn s.1⟩,⟨val s,h⟩),outside s h⟩
  let read : ↥U⊕V→X := Sum.elim Subtype.val (fun e:V => e.val.2.val)
  have back (s) : read (send s)=val s := by dsimp only [send];split <;> rfl
  have inj : Function.Injective send := by
    intro s t eq
    have same : val s=val t := (back s).symm.trans ((congrArg read eq).trans (back t))
    have vert := f.injective same
    have first := congrArg Sigma.fst vert
    have index := congrArg (fun z:Vertices n => z.2.val) vert
    apply Prod.ext (Subtype.ext first)
    apply idx.injective
    exact Fin.ext index
  have count := Nat.card_le_card_of_injective send inj
  rw [Nat.card_prod,Nat.card_fin,Nat.card_sum] at count
  change 3*B.ncard≤U.ncard+Nat.card V
  change B.ncard*3≤U.ncard+Nat.card V at count
  omega

#print axioms three_vertices_per_touched_star
end JSP452Audit.StarHost
