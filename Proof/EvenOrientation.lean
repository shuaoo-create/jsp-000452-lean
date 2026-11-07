import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Logic.Equiv.Prod

namespace JSP452Audit.StarHost
variable {E V : Type*} [Finite E]

/-- Numbering each incidence by one of two positions at a local slot
does not identify the two ends of a loop. -/
private theorem incidence_table (ends : E → Bool → V) (d : V → ℕ)
    (deg : ∀ v, Nat.card {i : E × Bool // ends i.1 i.2 = v} = 2 * d v) :
    ∃ chart : (E × Bool) ≃ ((Σ v, Fin (d v)) × Bool),
      ∀ i, (chart i).1.1 = ends i.1 i.2 := by
  classical
  let _ := Fintype.ofFinite E
  let g (i : E × Bool) := ends i.1 i.2
  let table (v : V) : {i : E × Bool // g i = v} ≃ Fin (d v) × Bool :=
    Fintype.equivOfCardEq (by simpa [g,Nat.card_eq_fintype_card,Nat.mul_comm] using deg v)
  let chart := ((Equiv.sigmaFiberEquiv g).symm.trans (Equiv.sigmaCongrRight table)).trans
    (Equiv.sigmaProdDistrib (fun v => Fin (d v)) Bool).symm
  exact ⟨chart,fun _ => rfl⟩

/-- Select one of the two positions of each edge so that each slot is used once. -/
private theorem slot_transversal {S : Type*} [Finite S] (chart : (E × Bool) ≃ (S × Bool)) :
    ∃ (f : E ≃ S) (pick : E → Bool), ∀ e, (chart (e,pick e)).1 = f e := by
  classical
  let _ := Fintype.ofFinite E
  let _ := Fintype.ofFinite S
  let N (e : E) := Finset.univ.image (fun b : Bool => (chart (e,b)).1)
  have hall (t : Finset E) : t.card ≤ (t.biUnion N).card := by
    let lift (p : t × Bool) : (t.biUnion N) × Bool :=
      (⟨(chart (p.1.val,p.2)).1,Finset.mem_biUnion.mpr ⟨p.1.val,p.1.property,
        Finset.mem_image.mpr ⟨p.2,Finset.mem_univ _,rfl⟩⟩⟩,(chart (p.1.val,p.2)).2)
    have inj : Function.Injective lift := by
      intro p q heq
      have z : chart (p.1.val,p.2) = chart (q.1.val,q.2) := Prod.ext
        (congrArg (fun u : (t.biUnion N) × Bool => u.1.val) heq) (congrArg (fun u : (t.biUnion N) × Bool => u.2) heq)
      obtain hz := chart.injective z
      exact Prod.ext (Subtype.ext (congrArg Prod.fst hz)) (congrArg (fun u : E × Bool => u.2) hz)
    have h := Nat.card_le_card_of_injective lift inj
    simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_bool, Fintype.card_coe, Nat.mul_le_mul_right_iff (by decide : 0 < 2)] using h
  obtain ⟨f,inj,mem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' N).mp hall
  have total : Nat.card E = Nat.card S := by
    simpa [Nat.card_eq_fintype_card] using Nat.card_congr chart
  let bij := Equiv.ofBijective f (inj.bijective_of_nat_card_le total.ge)
  have choose (e : E) : ∃ b, (chart (e,b)).1 = bij e := by
    obtain ⟨b,_,hb⟩ := Finset.mem_image.mp (mem e)
    exact ⟨b,hb⟩
  exact ⟨bij,fun e => (choose e).choose,fun e => (choose e).choose_spec⟩


/-- Distinguish the chosen and opposite endpoint at each edge, even on a loop. -/
theorem orientation_incident_count (ends : E → Bool → V) (pick : E → Bool) (v : V) :
    Nat.card {e // ends e (pick e) = v} + Nat.card {e // ends e (!(pick e)) = v} =
      Nat.card {i : E × Bool // ends i.1 i.2 = v} := by
  let I := {e // ends e (pick e) = v}
  let O := {e // ends e (!(pick e)) = v}
  let F := {i : E × Bool // ends i.1 i.2 = v}
  let f : I ⊕ O → F := Sum.elim (fun x => ⟨(x.val,pick x.val),x.property⟩)
    (fun x => ⟨(x.val,!(pick x.val)),x.property⟩)
  have distinct (x : I) (y : O) (h : f (.inl x) = f (.inr y)) : False := by
    have he : x.val = y.val := congrArg (fun p : F => p.val.1) h
    have hb : pick x.val = !(pick y.val) := congrArg (fun p : F => p.val.2) h
    rw [he] at hb
    cases ht : pick y.val <;> simp_all
  have inj : Function.Injective f := by
    rintro (x|x) (y|y) h
    · exact congrArg Sum.inl (Subtype.ext (congrArg (fun p : F => p.val.1) h))
    · exact (distinct x y h).elim
    · exact (distinct y x h.symm).elim
    · exact congrArg Sum.inr (Subtype.ext (congrArg (fun p : F => p.val.1) h))
  have surj : Function.Surjective f := by
    rintro ⟨⟨e,b⟩,hb⟩
    by_cases eq : b = pick e
    · subst b
      exact ⟨.inl ⟨e,hb⟩,rfl⟩
    · have other : b = !(pick e) := by cases b <;> cases hp : pick e <;> simp_all
      subst b
      exact ⟨.inr ⟨e,hb⟩,rfl⟩
  simpa only [Nat.card_sum] using Nat.card_eq_of_bijective f ⟨inj,surj⟩

/-- Every finite even incidence system admits an orientation with the prescribed
half-degree at every vertex. Parallel IDs and coincident endpoints are permitted. -/
theorem exists_even_orientation [Finite V] (ends : E → Bool → V) (d : V → ℕ)
    (deg : ∀ v, Nat.card {i : E × Bool // ends i.1 i.2 = v} = 2 * d v) :
    ∃ pick : E → Bool, ∀ v,
      Nat.card {e // ends e (pick e) = v} = d v ∧
      Nat.card {e // ends e (!(pick e)) = v} = d v := by
  obtain ⟨chart,labels⟩ := incidence_table ends d deg
  obtain ⟨f,pick,hp⟩ := slot_transversal chart
  have head (e : E) : ends e (pick e) = (f e).1 :=
    (labels (e,pick e)).symm.trans (congrArg Sigma.fst (hp e))
  refine ⟨pick,fun v => ?_⟩
  let fiber : {p : Σ w, Fin (d w) // p.1 = v} ≃ Fin (d v) := {
    toFun := fun ⟨⟨w,i⟩,h⟩ => h ▸ i
    invFun := fun i => ⟨⟨v,i⟩,rfl⟩
    left_inv := by rintro ⟨⟨w,i⟩,h⟩; cases h; rfl
    right_inv := by intro i; rfl }
  let atHead := Equiv.subtypeEquiv f (p := fun e => ends e (pick e) = v)
    (q := fun slot => slot.1 = v) (fun e => by rw [head])
  have incoming : Nat.card {e // ends e (pick e) = v} = d v := by
    simpa only [Nat.card_fin] using Nat.card_congr (atHead.trans fiber)
  have sum := orientation_incident_count ends pick v
  rw [deg v,incoming] at sum
  exact ⟨incoming,by omega⟩

#print axioms orientation_incident_count
#print axioms exists_even_orientation

#print axioms incidence_table
#print axioms slot_transversal
end JSP452Audit.StarHost
