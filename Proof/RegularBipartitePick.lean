import Mathlib.Combinatorics.Hall.Finite
import Mathlib.SetTheory.Cardinal.Finite

namespace JSP452Audit.StarHost

variable {E L R : Type*} [Finite E] [Finite L] [Finite R]

private theorem card_regular_preimage {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (k : ℕ) (deg : ∀ x, Nat.card {e // f e = x} = k) (S : Finset B) :
    (Finset.univ.filter (fun e => f e ∈ S)).card = S.card * k := by
  rw [← Finset.sum_card_fiberwise_eq_card_filter Finset.univ S f]
  exact Finset.sum_const_nat (fun x _ => by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using deg x)

/-- Choose actual edge IDs. Each left endpoint is used once, and their right
endpoints form a bijection. Parallel edges may witness the same adjacency. -/
theorem regular_bipartite_representatives (src : E → L) (dst : E → R)
    (k : ℕ) (pos : 0 < k)
    (left : ∀ x, Nat.card {e // src e = x} = k)
    (right : ∀ y, Nat.card {e // dst e = y} = k) :
    ∃ pick : L → E, (∀ x, src (pick x) = x) ∧ Function.Bijective (dst ∘ pick) := by
  classical
  let _ := Fintype.ofFinite E
  let _ := Fintype.ofFinite L
  let _ := Fintype.ofFinite R
  let nbr (x : L) : Finset R := (Finset.univ.filter (fun e : E => src e = x)).image dst
  have mem (x : L) (y : R) : y ∈ nbr x ↔ ∃ e, src e = x ∧ dst e = y := by
    simp [nbr]
  have hall (S : Finset L) : S.card ≤ (S.biUnion nbr).card := by
    have sub : Finset.univ.filter (fun e : E => src e ∈ S) ⊆
        Finset.univ.filter (fun e : E => dst e ∈ S.biUnion nbr) := by
      intro e he
      have hs := (Finset.mem_filter.mp he).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_biUnion.mpr
        ⟨src e,hs,(mem _ _).mpr ⟨e,rfl,rfl⟩⟩⟩
    have bound := Finset.card_le_card sub
    rw [card_regular_preimage src k left,card_regular_preimage dst k right] at bound
    exact Nat.le_of_mul_le_mul_right bound pos
  obtain ⟨mate, inj, hits⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' nbr).mp hall
  have leftTotal : Fintype.card E = Fintype.card L * k := by
    simpa using card_regular_preimage src k left Finset.univ
  have rightTotal : Fintype.card E = Fintype.card R * k := by
    simpa using card_regular_preimage dst k right Finset.univ
  have cards : Nat.card L = Nat.card R := by
    simpa only [Nat.card_eq_fintype_card] using
      Nat.eq_of_mul_eq_mul_right pos (leftTotal.symm.trans rightTotal)
  have bij := (Nat.bijective_iff_injective_and_card mate).mpr ⟨inj,cards⟩
  choose pick hl hr using (fun x => (mem x (mate x)).mp (hits x))
  have same : dst ∘ pick = mate := funext hr
  exact ⟨pick,hl,same.symm ▸ bij⟩

/-- A layer of the original edge set with exactly one selected edge at
every left and every right endpoint. No inhabitedness assumption is needed. -/
theorem regular_bipartite_pick {k : ℕ} (src : E → L) (dst : E → R) (pos : 0 < k)
    (left : ∀ x, Nat.card {e // src e = x} = k)
    (right : ∀ y, Nat.card {e // dst e = y} = k) :
    ∃ A : Set E,
      (∀ x, Nat.card {e : E // e ∈ A ∧ src e = x} = 1) ∧
      (∀ y, Nat.card {e : E // e ∈ A ∧ dst e = y} = 1) := by
  obtain ⟨pick,hs,hd⟩ := regular_bipartite_representatives src dst k pos left right
  refine ⟨Set.range pick,?_,?_⟩
  · intro x
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨pick x,⟨x,rfl⟩,hs x⟩,?_⟩
    rintro ⟨_,⟨z,rfl⟩,hz⟩
    exact Subtype.ext (congrArg pick ((hs z).symm.trans hz))
  · intro y
    obtain ⟨x,hx⟩ := hd.surjective y
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨pick x,⟨x,rfl⟩,hx⟩,?_⟩
    rintro ⟨_,⟨z,rfl⟩,hz⟩
    exact Subtype.ext (congrArg pick (hd.injective (hz.trans hx.symm)))

#print axioms regular_bipartite_representatives
#print axioms regular_bipartite_pick
end JSP452Audit.StarHost
