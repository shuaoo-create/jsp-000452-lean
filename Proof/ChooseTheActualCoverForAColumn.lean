import TwoColoredEdgePaletteRestoration
namespace JSP452Audit.StarHost.NinePortRegion
open SimpleGraph
universe u
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)

noncomputable abbrev coverFee (b B : ℕ) :=
  max (R.portCount+B-1) (2*R.totalCapacity+4-R.portCount-b*B)

theorem choose_cover_palette (b B : ℕ) (positive : 0<B) :
    ∃S : Set X,R.paidTips⊆S ∧ S⊆R.chosen ∧
      S.ncard+(B-1)≤R.coverFee b B ∧
      ∀A : SimpleGraph X,A≤R.erased → ∀k,∀f : (forest (fun _ : Fin k => b)).Copy (A⊔R.coverBlue S),
        (touchedStars A (R.coverBlue S) (fun _ : Fin k => b) f).ncard≤B-1 := by
  classical
  let w := 2*R.totalCapacity+4-R.portCount
  let need := w+1-(b+1)*B
  let k := min R.chosen.ncard (max R.paidTips.ncard need)
  obtain ⟨inside,tips,roots⟩ := R.physical_tip_and_root_counts
  have left : R.paidTips.ncard≤k := le_min (Set.ncard_le_ncard inside) (Nat.le_max_left _ _)
  obtain ⟨S,has,sub,sz⟩ := Set.exists_subsuperset_card_eq inside left (Nat.min_le_left _ _)
  have mult : (b+1)*B=b*B+B := by rw [Nat.add_mul,Nat.one_mul]
  have fee : k+(B-1)≤R.coverFee b B := by
    change k+(B-1)≤max (R.portCount+B-1) (w-b*B)
    dsimp only [k,need];omega
  refine ⟨S,has,sub,sz ▸ fee,?_⟩
  intro A le j f
  let T := touchedStars A (R.coverBlue S) (fun _ : Fin j => b) f
  change T.ncard≤B-1
  obtain ⟨pack,all⟩ := R.cover_blue_damage S has sub A le b f
  change (b+1)*T.ncard+S.ncard+R.portCount≤2*R.totalCapacity+4 at pack
  change S.ncard=R.chosen.ncard → T.ncard=0 at all
  by_cases full : S.ncard=R.chosen.ncard
  · rw [all full];omega
  · have level : need≤S.ncard := by dsimp only [k] at sz;omega
    have budget : (b+1)*T.ncard+S.ncard≤w := by dsimp only [w];omega
    by_contra! many
    have lower := Nat.mul_le_mul_left (b+1) (show B≤T.ncard by omega)
    dsimp only [need] at level
    omega

theorem cover_original_rectangle {s t r a b : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pa : 0<a) (pb : 0<b)
    (blue : 0<originalThresholdCount m b) (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    originalThresholdCount n a+originalThresholdCount m b-1-r≤
      uniformEnvelope R.erased (a+b-1)+R.coverFee b (originalThresholdCount m b) := by
  let A := originalThresholdCount n a
  let B := originalThresholdCount m b
  obtain ⟨S,_,_,size,limit⟩ := R.choose_cover_palette b B blue
  change S.ncard+(B-1)≤R.coverFee b B at size
  change A+B-1-r≤uniformEnvelope R.erased (a+b-1)+R.coverFee b B
  by_cases live : S.ncard<A
  · have red (J : SimpleGraph X) (_ : J≤R.erased) (k) (f : (forest (fun _ : Fin k => a)).Copy (J⊔R.coverRed S)) :
        (touchedStars J (R.coverRed S) (fun _ : Fin k => a) f).ncard≤S.ncard :=
      (touchedStars_le_matchingEdges J (R.coverRed S) _ f).trans (R.cover_red_rank S)
    have copy := two_palette_typed_restoration G R.erased (R.coverRed S) (R.coverBlue S) sdiff_le
      (sdiff_le.trans R.adapted_le) (R.cover_palette_spans S) n m hn hm live
      (show B-1<B by change 0<B at blue;omega) red limit row
    have fee := R.typed_width_envelope pa pb rfl copy
    change A+B-1-r-S.ncard-(B-1)≤uniformEnvelope R.erased (a+b-1) at fee
    omega
  · change 0<B at blue
    omega

#print axioms choose_cover_palette
#print axioms cover_original_rectangle
end JSP452Audit.StarHost.NinePortRegion
