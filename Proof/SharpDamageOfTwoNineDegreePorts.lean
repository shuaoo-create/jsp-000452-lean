import OrdinaryAndExceptionalStarPacking
namespace JSP452Audit.StarHost.NinePortRegion
open SimpleGraph JSP452Audit.Padded
universe u
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)

noncomputable abbrev slotDamage (a : ℕ) :=
  R.portCount+(2*R.totalCapacity+4-2*R.portCount)/(a+1)

theorem actual_port_star_damage {I : Type*} [Finite I] (A : SimpleGraph X) (sub : A≤R.erased) (a : ℕ)
    (f : (forest (fun _ : I => a)).Copy (A⊔R.adapted)) :
    (touchedStars A R.adapted (fun _ : I => a) f).ncard≤R.slotDamage a := by
  classical
  let n := fun _ : I => a
  let T := touchedStars A R.adapted n f
  let E : Set I := {i | i∈T ∧ ∃j : Fin (a+1),f ⟨i,j⟩∈R.paidTips}
  let N := T\E
  let U := R.chosen∪R.looseRoots
  have cut : E⊆T := fun _ h => h.1
  have apart : Disjoint N E := Set.disjoint_left.mpr (fun _ h e => h.2 e)
  have incl : A⊔R.adapted≤G := sup_le (sub.trans sdiff_le) R.adapted_le
  obtain ⟨tipSub,tipCost,rootCost⟩ := R.physical_tip_and_root_counts
  have normal (i) (member : i∈N) (j : Fin (a+1)) : f ⟨i,j⟩∈U := by
    have avoid (k : Fin (a+1)) : f ⟨i,k⟩∉R.paidTips := fun h => member.2 ⟨member.1,k,h⟩
    obtain ⟨l,miss⟩ := member.1
    have marked := (f.toHom.map_adj (starEdge n ⟨i,l⟩)).resolve_left miss
    have centerIn := (R.adapted_center_or_paid_leaf marked).resolve_right (avoid l.succ)
    refine Fin.cases (Or.inl centerIn) (fun leaf => ?_) j
    exact R.neighbor_of_ordinary_center centerIn (avoid 0) (incl (f.toHom.map_adj (starEdge n ⟨i,leaf⟩)))
  have exception (i) (mem : i∈E) : ∃j : Fin (a+1),f ⟨i,j⟩∈R.paidTips := mem.2
  obtain ⟨few,packed⟩ := packed_star_classes _ a f N E apart U R.paidTips normal exception
    (tipSub.trans Set.subset_union_left)
  have pts := Set.ncard_union_le R.chosen R.looseRoots
  change U.ncard≤R.chosen.ncard+R.looseRoots.ncard at pts
  rw [R.chosen_structure.1] at pts
  let e := R.portCount
  let w := 2*R.totalCapacity+4-2*e
  have eLe : E.ncard≤e := few.trans tipCost
  have twice : 2*e≤2*R.totalCapacity+4 := by
    change R.looseRoots.ncard+e≤2 at rootCost;omega
  have sz := Set.ncard_sdiff_add_ncard_of_subset cut
  change N.ncard+E.ncard=T.ncard at sz
  have sum : (a+1)*T.ncard=(a+1)*N.ncard+E.ncard+a*E.ncard := by
    rw [←sz,Nat.mul_add,add_mul a 1 E.ncard];omega
  have extra := Nat.mul_le_mul_left a eLe
  have bound : (a+1)*T.ncard≤(a+1)*e+w := by
    rw [sum,Nat.add_mul a 1 e,Nat.one_mul]
    dsimp only [w]
    change R.looseRoots.ncard+e≤2 at rootCost
    omega
  change T.ncard≤e+w/(a+1)
  by_cases le : T.ncard≤e
  · exact le.trans (Nat.le_add_right _ _)
  · have shifted : (T.ncard-e)*(a+1)≤w := by
      have eq : (a+1)*T.ncard=(a+1)*e+(T.ncard-e)*(a+1) := by
        rw [Nat.mul_comm (T.ncard-e) _,←Nat.mul_add];congr 1;omega
      omega
    have div := (Nat.le_div_iff_mul_le (show 0<a+1 by omega)).mpr shifted
    omega

#print axioms actual_port_star_damage
end JSP452Audit.StarHost.NinePortRegion
