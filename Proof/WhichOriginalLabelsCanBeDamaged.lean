import RealNineEightSevenInventory
namespace JSP452Audit.StarHost.NinePortRegion
open SimpleGraph
universe u
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)

def paidTip (i : Fin 2) : Set X := {v | R.essential i ∧ v=(R.port i).tip}
def looseRoot (i : Fin 2) : Set X := {v | ¬R.essential i ∧ v=(R.port i).root}
abbrev paidTips := R.paidTip 0∪R.paidTip 1
abbrev looseRoots := R.looseRoot 0∪R.looseRoot 1

theorem all_paid_tip_mem (i : Fin 2) (e : R.essential i) : (R.port i).tip∈R.paidTips := by
  fin_cases i
  · exact Or.inl ⟨e,rfl⟩
  · exact Or.inr ⟨e,rfl⟩

theorem all_loose_root_mem (i : Fin 2) (e : ¬R.essential i) : (R.port i).root∈R.looseRoots := by
  fin_cases i
  · exact Or.inl ⟨e,rfl⟩
  · exact Or.inr ⟨e,rfl⟩

theorem physical_tip_and_root_counts :
    R.paidTips⊆R.chosen ∧ R.paidTips.ncard≤R.portCount ∧ R.looseRoots.ncard+R.portCount≤2 := by
  classical
  have count (i : Fin 2) : (R.paidTip i).ncard=R.portCharge i ∧
      (R.looseRoot i).ncard+R.portCharge i=1 := by
    by_cases he : R.essential i
    · have t : R.paidTip i={(R.port i).tip} := by ext x;simp [paidTip,he]
      have l : R.looseRoot i=∅ := by ext x;simp [looseRoot,he]
      simp [t,l,portCharge,he]
    · have t : R.paidTip i=∅ := by ext x;simp [paidTip,he]
      have l : R.looseRoot i={(R.port i).root} := by ext x;simp [looseRoot,he]
      simp [t,l,portCharge,he]
  have t := Set.ncard_union_le (R.paidTip 0) (R.paidTip 1)
  have l := Set.ncard_union_le (R.looseRoot 0) (R.looseRoot 1)
  have left := count 0
  have right := count 1
  change R.paidTips.ncard≤_ at t
  change R.looseRoots.ncard≤_ at l
  refine ⟨?_,?_,?_⟩
  · rintro x (h|h)
    · exact Or.inl (h.2.symm ▸ (R.port 0).tip_mem)
    · exact Or.inr (h.2.symm ▸ (R.port 1).tip_mem)
  · dsimp only [portCount];omega
  · dsimp only [portCount];omega

theorem adapted_center_or_paid_leaf {x y : X} (adj : R.adapted.Adj x y) : x∈R.chosen ∨ y∈R.paidTips := by
  have side (i : Fin 2) (inc : R.box i⊆R.chosen) (edge : (R.portPart i).Adj x y) :
      x∈R.chosen ∨ y∈R.paidTips := by
    rcases (R.portPart_edges i x y).mp edge with inner|⟨he,ends⟩
    · exact Or.inl (inc ((portInside_adj G (R.box i) x y).mp inner).2.1)
    · rcases ends with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact Or.inl (inc (R.port i).tip_mem)
      · exact Or.inr (R.all_paid_tip_mem i he)
  exact adj.elim (side 0 Set.subset_union_left) (side 1 Set.subset_union_right)

theorem neighbor_of_ordinary_center {x y : X} (ins : x∈R.chosen) (away : x∉R.paidTips) (edge : G.Adj x y) :
    y∈R.chosen∪R.looseRoots := by
  have side (i : Fin 2) (xin : x∈R.box i) (inc : R.box i⊆R.chosen) : y∈R.chosen∪R.looseRoots := by
    by_cases yin : y∈R.box i
    · exact Or.inl (inc yin)
    · obtain ⟨xt,yr⟩ := (R.port i).only x xin y yin edge
      have loose : ¬R.essential i := fun he => away (xt.symm ▸ R.all_paid_tip_mem i he)
      exact Or.inr (yr.symm ▸ R.all_loose_root_mem i loose)
  exact ins.elim (fun h => side 0 h Set.subset_union_left) (fun h => side 1 h Set.subset_union_right)

#print axioms all_paid_tip_mem
#print axioms all_loose_root_mem
#print axioms physical_tip_and_root_counts
#print axioms adapted_center_or_paid_leaf
#print axioms neighbor_of_ordinary_center
end JSP452Audit.StarHost.NinePortRegion
