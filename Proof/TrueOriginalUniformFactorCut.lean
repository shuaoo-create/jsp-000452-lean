import OriginalFailureOnlyDoubleEscape
import BlueExcessObstruction
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

noncomputable def originalFactorCut {X : Type u} [Finite X] (G : SimpleGraph X) (p q : ℕ) (S T : Set X) : ℤ := by
  classical
  let _ := Fintype.ofFinite X
  let P : JSP452Audit.Padded.Spec X := ⟨G,fun _ => p,fun _ => q,false⟩
  exact P.cutDeficit S T

/-- A genuine uniform corner supplies disjoint sets in the original
finite graph. Its full width survives in the signed factor deficit. -/
theorem original_uniform_factor_cut {X : Type u} [Finite X] (G : SimpleGraph X) (x y v w : ℕ)
    (rx : 0<x) (by' : 0<y) (pv : 0<v) (pw : 0<w)
    (cap : ∀z,Nat.card (G.neighborSet z)≤(x-1)+(y-1))
    (forced : Forces G (forest (fun _ : Fin v => x)) (forest (fun _ : Fin w => y))) :
    ∃S T:Set X,Disjoint S T ∧ ((v+w-1:ℕ):ℤ)≤originalFactorCut G (x-1) (y-1) S T := by
  classical
  let _ := Fintype.ofFinite X
  let P : JSP452Audit.Padded.Spec X := ⟨G,fun _ => x-1,fun _ => y-1,false⟩
  have caps (z:X) : P.G.degree z≤P.A z+P.B z := by
    change G.degree z≤(x-1)+(y-1)
    simpa only [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree] using cap z
  have xr : x-1+1≤x := by omega
  have yb : y-1+1≤y := by omega
  have xc : v≤((Finset.univ:Finset (Fin v)).filter (fun _ => x-1+1≤x)).card := by
    have eq : ((Finset.univ:Finset (Fin v)).filter (fun _ => x-1+1≤x))=Finset.univ := Finset.filter_true_of_mem (fun _ _ => xr)
    rw [eq];simp
  have yc : w≤((Finset.univ:Finset (Fin w)).filter (fun _ => y-1+1≤y)).card := by
    have eq : ((Finset.univ:Finset (Fin w)).filter (fun _ => y-1+1≤y))=Finset.univ := Finset.filter_true_of_mem (fun _ _ => yb)
    rw [eq];simp
  obtain ⟨S,T,apart,score⟩ := P.exists_original_cut_of_forcing_large_stars (p:=x-1) (q:=y-1) caps (fun _ => rfl) (fun _ => rfl)
    pv pw (fun _:Fin v => x) (fun _:Fin w => y) xc yc forced
  exact ⟨S,T,apart,score⟩

#print axioms original_uniform_factor_cut
end JSP452Audit.StarHost