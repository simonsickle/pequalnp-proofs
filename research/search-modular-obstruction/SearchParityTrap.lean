import PEqualNP.Defs

namespace SearchParityTrap
open PEqualNP.Search PEqualNP.ProofComplexity

abbrev V := Fin 3 × Fin 1
def a : V := (0, 0)
def b : V := (1, 0)
def c : V := (2, 0)
def lit (v : V) (s : Bool) : QEq V := litQEq (v, s)
abbrev D := IsResLinQSynDerivation (BPHP 3 1)

theorem clause (i j : Fin 3) (h : i ≠ j) (s : Bool) :
    ({((i, 0), s), ((j, 0), s)} : Clause V) ∈ BPHP 3 1 := by
  refine ⟨i, j, (fun _ => !s), h, ?_⟩
  ext z
  simp [Fin.fin_one_eq_zero]

theorem addAxiom (π : List (QLine V)) (hπ : D π) (i j : Fin 3) (h : i ≠ j) (s : Bool) :
    D ([lit (i, 0) s, lit (j, 0) s] :: π) := by
  apply IsResLinQSynDerivation.ax ({((i, 0), s), ((j, 0), s)} : Clause V) hπ (clause i j h s)
  intro e
  simp [lit]

theorem qres (π : List (QLine V)) (hπ : D π) (v : V) (s : Bool)
    (C E : QLine V) (hC : lit v s :: C ∈ π) (hE : lit v (!s) :: E ∈ π) :
    ∃ σ : List (QLine V), D σ ∧ C ++ E ∈ σ ∧ ∀ L ∈ π, L ∈ σ := by
  let e : QEq V := (0, if s then 1 else -1)
  have hcomb : ((1 : ℤ) • (lit v s).1 + (-1 : ℤ) • (lit v (!s)).1,
      (1 : ℤ) * (lit v s).2 + (-1 : ℤ) * (lit v (!s)).2) = e := by
    cases s <;> ext u <;> simp [e, lit, litQEq]
  have hne : e.2 ≠ 0 := by cases s <;> norm_num [e]
  have h₁ : D ((e :: (C ++ E)) :: π) := by
    simpa only [hcomb] using IsResLinQSynDerivation.res 1 (-1) hπ hC hE
  let L := (e :: (C ++ E)).filter (fun q : QEq V => ¬ (q.1 = 0 ∧ q.2 ≠ 0))
  have h₂ : D (L :: (e :: (C ++ E)) :: π) :=
    IsResLinQSynDerivation.simp h₁ (by simp)
  let σ := (C ++ E) :: L :: (e :: (C ++ E)) :: π
  have h₃ : D σ := by
    apply IsResLinQSynDerivation.weaken h₂ (by simp : L ∈ L :: (e :: (C ++ E)) :: π)
    intro f hf
    have hh := List.mem_filter.mp hf
    rcases List.mem_cons.mp hh.1 with heq | h
    · exact ((of_decide_eq_true hh.2) ⟨congrArg Prod.fst heq, by simpa [heq] using hne⟩).elim
    · exact h
  refine ⟨σ, h₃, by simp [σ], ?_⟩
  intro y hy
  simp [σ, hy]

theorem collapse (π : List (QLine V)) (hπ : D π) (q : QEq V) (hq : [q, q] ∈ π) :
    D ([q] :: π) := by
  apply IsResLinQSynDerivation.weaken hπ hq
  simp

theorem bphp_one_derived_units :
    ∃ π : List (QLine V), D π ∧ [lit a false] ∈ π ∧ [lit a true] ∈ π := by
  have h₀ : D ([] : List (QLine V)) := .nil
  have h₁ := addAxiom _ h₀ 1 0 (by decide) true
  have h₂ := addAxiom _ h₁ 1 2 (by decide) false
  have h₃ := addAxiom _ h₂ 2 0 (by decide) true
  have h₄ := addAxiom _ h₃ 1 0 (by decide) false
  have h₅ := addAxiom _ h₄ 1 2 (by decide) true
  have h₆ := addAxiom _ h₅ 2 0 (by decide) false
  obtain ⟨π, hp, hn, keep⟩ := qres _ h₆ b true [lit a true] [lit c false]
    (by simp [a,b]) (by simp [b,c])
  have swap₁ : D ([lit c false, lit a true] :: π) := by
    apply IsResLinQSynDerivation.weaken hp hn
    simp [or_comm]
  obtain ⟨π₁, hp₁, hdup, keep₁⟩ := qres _ swap₁ c false [lit a true] [lit a true]
    (by simp) (by exact List.mem_cons_of_mem _ (keep _ (by simp [a,c])))
  have single₁ := collapse _ hp₁ (lit a true) hdup
  have lift (L : QLine V) (H : L ∈ _) : L ∈ [lit a true] :: π₁ :=
    List.mem_cons_of_mem _ (keep₁ _ (List.mem_cons_of_mem _ (keep _ H)))
  obtain ⟨π₂, hp₂, hn₂, keep₂⟩ := qres _ single₁ b false [lit a false] [lit c true]
    (lift _ (by simp [a,b])) (lift _ (by simp [b,c]))
  have swap₂ : D ([lit c true, lit a false] :: π₂) := by
    apply IsResLinQSynDerivation.weaken hp₂ hn₂
    simp [or_comm]
  obtain ⟨π₃, hp₃, hdup₃, keep₃⟩ := qres _ swap₂ c true [lit a false] [lit a false]
    (by simp) (by exact List.mem_cons_of_mem _ (keep₂ _ (lift _ (by simp [a,c]))))
  refine ⟨[lit a false] :: π₃, collapse _ hp₃ _ hdup₃, by simp, ?_⟩
  exact List.mem_cons_of_mem _ (keep₃ _ (List.mem_cons_of_mem _ (keep₂ _ (by simp))))

theorem modular_trap (m : ℕ) (hm : m ≠ 0) :
    ∃ π : List (QLine V), IsResLinQSynRefutation (BPHP 3 1) π ∧
      ([(0, (m : ℤ))] : QLine V) ∈ π ∧
      (0 : ZMod m) = (m : ZMod m) := by
  obtain ⟨π, hp, hf, ht⟩ := bphp_one_derived_units
  have hcomb : ((m : ℤ) • (lit a true).1 + (-(m : ℤ)) • (lit a false).1,
      (m : ℤ) * (lit a true).2 + (-(m : ℤ)) * (lit a false).2) = ((0, (m : ℤ)) : QEq V) := by
    ext u <;> simp [lit, litQEq]
  have h₁ : D (([(0,(m : ℤ))] : QLine V) :: π) := by
    simpa only [hcomb, List.nil_append] using IsResLinQSynDerivation.res (m : ℤ) (-(m : ℤ)) hp ht hf
  have h₂ : D ([] :: ([(0,(m : ℤ))] : QLine V) :: π) := by
    simpa [hm] using IsResLinQSynDerivation.simp h₁ (by simp :
      ([(0,(m : ℤ))] : QLine V) ∈ ([(0,(m : ℤ))] : QLine V) :: π)
  refine ⟨_, ⟨h₂, by simp⟩, by simp, by simp⟩

theorem finite_fixed_moduli_trap (ms : Finset Nat) (hms : ∀ m ∈ ms, m ≠ 0) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ π : List (QLine V), IsResLinQSynRefutation (BPHP 3 1) π ∧
      ([(0, (n : ℤ))] : QLine V) ∈ π ∧
      ∀ m ∈ ms, (n : ZMod m) = 0 := by
  let n := ∏ m ∈ ms, m
  have hn : n ≠ 0 := Finset.prod_ne_zero_iff.mpr hms
  obtain ⟨π, hπ, heq, _⟩ := modular_trap n hn
  refine ⟨n, hn, π, hπ, heq, ?_⟩
  intro m hm
  exact (ZMod.natCast_eq_zero_iff n m).mpr (Finset.dvd_prod_of_mem id hm)

end SearchParityTrap
