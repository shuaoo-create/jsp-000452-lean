import InternalEndpointsOfTheActualTenDegreePorts
namespace JSP452Audit.StarHost.TenPortSupport
open SimpleGraph JSP452Audit.Padded
universe u
variable {X : Type u} [Finite X] {G : SimpleGraph X} {K:TenBlockPartition G} {q:ℕ} (R : TenPortSupport G K q)

noncomputable abbrev slotDamage (a : ℕ) :=
  R.portCount+(R.support.ncard-R.portCount)/(a+1)

theorem actual_port_star_damage {I : Type*} [Finite I] (A : SimpleGraph X) (sub : A≤(G \ R.piece)) (a : ℕ)
    (f : (forest (fun _ : I => a)).Copy (A⊔R.piece)) :
    (touchedStars A R.piece (fun _ : I => a) f).ncard≤R.slotDamage a := by
  classical
  let n := fun _ : I => a
  let T := touchedStars A R.piece n f
  let E : Set I := {i | i∈T ∧ ∃j : Fin (a+1),f ⟨i,j⟩∈R.innerTips}
  let N := T\E
  let U := R.support
  have cut : E⊆T := fun _ h => h.1
  have apart : Disjoint N E := Set.disjoint_left.mpr (fun _ h e => h.2 e)
  have incl : A⊔R.piece≤G := sup_le (sub.trans sdiff_le) (eraseInternal_le G _)
  have tipSub : R.innerTips⊆U := fun _ mem => mem.1
  have tipCost := R.tip_count
  have normal (i) (member : i∈N) (j : Fin (a+1)) : f ⟨i,j⟩∈U := by
    have avoid (k : Fin (a+1)) : f ⟨i,k⟩∉R.innerTips := fun h => member.2 ⟨member.1,k,h⟩
    obtain ⟨l,miss⟩ := member.1
    have marked := (f.toHom.map_adj (starEdge n ⟨i,l⟩)).resolve_left miss
    have centerIn := (R.ordinary_center_or_marked_leaf marked).resolve_right (avoid l.succ)
    refine Fin.cases centerIn (fun leaf => ?_) j
    exact R.ordinary_neighbors_stay centerIn (avoid 0) (incl (f.toHom.map_adj (starEdge n ⟨i,leaf⟩)))
  have exception (i) (mem : i∈E) : ∃j : Fin (a+1),f ⟨i,j⟩∈R.innerTips := mem.2
  obtain ⟨few,packed⟩ := packed_star_classes _ a f N E apart U R.innerTips normal exception
    tipSub
  let e := R.portCount
  let w := R.support.ncard-e
  have eLe : E.ncard≤e := few.trans tipCost
  have cover : e≤R.support.ncard := by have bound := R.defect;have size := R.orderFloor;change R.targetDefect+e≤2 at bound;omega
  change (a+1)*N.ncard+E.ncard≤R.support.ncard at packed
  have sz := Set.ncard_sdiff_add_ncard_of_subset cut
  change N.ncard+E.ncard=T.ncard at sz
  have sum : (a+1)*T.ncard=(a+1)*N.ncard+E.ncard+a*E.ncard := by
    rw [←sz,Nat.mul_add,add_mul a 1 E.ncard];omega
  have extra := Nat.mul_le_mul_left a eLe
  have bound : (a+1)*T.ncard≤(a+1)*e+w := by
    rw [sum,Nat.add_mul a 1 e,Nat.one_mul]
    dsimp only [w]
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
end JSP452Audit.StarHost.TenPortSupport
