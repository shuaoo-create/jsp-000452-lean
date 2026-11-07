import EvenDeletionsInTheTwoOriginalOddBoxes
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem unit_star_from_named_edge {X : Type*} {G : SimpleGraph X} {v w : X} (edge : G.Adj v w) :
    (oneStar 1).IsContained G := by
  let send (z : Vertices (fun _ : Fin 1 => 1)) : X := if z.2.val=0 then v else w
  have inj : Function.Injective send := by
    rintro ⟨i,a⟩ ⟨j,b⟩ eq
    obtain rfl : j=i := Subsingleton.elim _ _
    fin_cases a <;> fin_cases b <;> simp_all [send,edge.ne,edge.ne.symm]
  refine ⟨{toHom := {toFun := send,map_rel' := ?_},injective' := inj}⟩
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  obtain rfl : j=i := Subsingleton.elim _ _
  have ne := h.ne
  fin_cases a <;> fin_cases b <;> simp_all [send,edge,edge.symm]

theorem uniform_copy_costs_unit_width {X : Type*} [Finite X] (Y : SimpleGraph X) (u h : ℕ) (ph : 0<h)
    (copy : (forest (fun _ : Fin u => h)).IsContained Y) : u≤uniformEnvelope Y h := by
  classical
  by_cases live : 0<u
  · have pair : Forces Y (forest (fun _ : Fin u => h)) (oneStar 1) := by
      intro A sub
      by_cases all : Y≤A
      · exact Or.inl (copy.mono_right all)
      · have some : ∃x y,Y.Adj x y ∧ ¬A.Adj x y := by
          by_contra! no
          exact all (fun x y edge => no x y edge)
        obtain ⟨x,y,e,m⟩ := some
        exact Or.inr (unit_star_from_named_edge (show (Y\A).Adj x y from ⟨e,m⟩))
    have bound := uniform_pair_le_envelope Y h 1 u 1 h ph (by decide) live (by decide) (by omega) pair
    omega
  · omega

theorem full_blue_avoidance_red_suffix {X : Type*} [Finite X] (G A : SimpleGraph X) (sub : A≤G)
    {s t r h : ℕ} (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) (alive : r<originalThresholdCount n h)
    (no : ¬(forest m).IsContained (G\A)) :
    (forest (fun _ : Fin (originalThresholdCount n h-r) => h)).IsContained A := by
  have len := original_threshold_le_length n h
  have use := row r 0 (s-r) t (by omega) (by omega) (by omega) (by omega) ht
  have exactM : (fun i : Fin t => padDemand m (0+i.val))=m := by funext i;simp [padDemand,i.isLt]
  rcases use A sub with red|blue
  · exact (uniform_inside_original_suffix n hn (show r+(s-r)=s by omega)
      (show r+(originalThresholdCount n h-r)≤originalThresholdCount n h by omega)).trans red
  · change (forest (fun i : Fin t => padDemand m (0+i.val))).IsContained _ at blue
    rw [exactM] at blue
    exact (no blue).elim

#print axioms unit_star_from_named_edge
#print axioms uniform_copy_costs_unit_width
#print axioms full_blue_avoidance_red_suffix
end JSP452Audit.StarHost
