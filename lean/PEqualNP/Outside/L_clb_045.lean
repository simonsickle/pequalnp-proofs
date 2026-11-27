import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_045
open PEqualNP.CircuitLowerBounds

def idxT (n w i v : ℕ) : ℕ :=
  ∑ p ∈ Finset.range (w + 1), if v.testBit ((i + p) % n - i) then 2 ^ p else 0

def idxF (n w d i r h : ℕ) : ℕ :=
  ∑ p ∈ Finset.range (w + 1),
    if (if n - d ≤ (i + p) % n then h.testBit ((i + p) % n - (n - d)) else r.testBit ((i + p) % n))
    then 2 ^ p else 0

def g (n m w d e : ℕ) (T : ℕ → ℕ → Bool) (A : ℕ → Bool → Bool) (t r v : ℕ) : Bool :=
  A t (v.testBit d) && (decide (t < e → v.testBit d = r.testBit t)) &&
    (if d ≤ t ∧ t - d < m then T (t - d) (idxT n w (t - d) v) else true)

def c (n m w d e : ℕ) (T : ℕ → ℕ → Bool) (A : ℕ → Bool → Bool) : ℕ → ℕ → ℕ → ℕ
  | 0, _, h => if h = 0 then 1 else 0
  | t + 1, r, h =>
      (if g n m w d e T A t r (2 * h) then c n m w d e T A t r ((2 * h) % 2 ^ d) else 0) +
      (if g n m w d e T A t r (2 * h + 1) then c n m w d e T A t r ((2 * h + 1) % 2 ^ d) else 0)

def F (n m w d : ℕ) (T : ℕ → ℕ → Bool) (r h : ℕ) : Bool :=
  (List.range m).all fun i => decide (n ≤ i + d) → T i (idxF n w d i r h)

def total (n m w d e : ℕ) (T : ℕ → ℕ → Bool) (A : ℕ → Bool → Bool) : ℕ :=
  ∑ r ∈ Finset.range (2 ^ e), ∑ h ∈ Finset.range (2 ^ d),
    if F n m w d T r h then c n m w d e T A n r h else 0

def CombStatement : Prop :=
  ∀ (n m w : ℕ) (hn : 0 < n) (hm : 0 < m), m ≤ n →
    ∀ (table : Fin m → (Fin (w + 1) → Bool) → Bool) (allow : Fin n → Bool → Bool),
      (Finset.univ.filter (fun z : Fin (2 ^ n) =>
        (∀ j : Fin n, allow j (z.val.testBit j.val) = true) ∧
        ∀ i : Fin m, table i (fun p => z.val.testBit ((i.val + p.val) % n)) = true)).card
      = total n m w (min w (n - 1)) (m + min w (n - 1) - n)
          (fun i a => table ⟨i % m, Nat.mod_lt _ hm⟩ (fun b => a.testBit b.val))
          (fun j b => allow ⟨j % n, Nat.mod_lt _ hn⟩ b)

noncomputable def cbInd (p : Prop) : ℕ := @ite ℕ p (Classical.propDecidable p) 1 0

theorem cbInd_pos {p : Prop} (h : p) : cbInd p = 1 := by
  unfold cbInd; exact ite_eq_left h

theorem cbInd_neg {p : Prop} (h : ¬p) : cbInd p = 0 := by
  unfold cbInd; exact ite_eq_right h

theorem cbInd_and (p q : Prop) : cbInd (p ∧ q) = cbInd p * cbInd q := by
  by_cases hp : p
  · by_cases hq : q
    · rw [cbInd_pos hp, cbInd_pos hq, cbInd_pos ⟨hp, hq⟩]
    · rw [cbInd_neg hq, cbInd_neg (fun h => hq h.2), Nat.mul_zero]
  · rw [cbInd_neg hp, cbInd_neg (fun h => hp h.1), Nat.zero_mul]

theorem cbInd_congr {p q : Prop} (h : p ↔ q) : cbInd p = cbInd q := by
  rw [propext h]

theorem cbInd_ite (p : Prop) [Decidable p] : cbInd p = if p then 1 else 0 := by
  by_cases hp : p
  · rw [cbInd_pos hp, ite_eq_left hp]
  · rw [cbInd_neg hp, ite_eq_right hp]

theorem cb_bitsum (f : ℕ → Bool) (k : ℕ) :
    (∑ p ∈ Finset.range k, if f p then 2 ^ p else 0) < 2 ^ k ∧
    ∀ q, (∑ p ∈ Finset.range k, if f p then 2 ^ p else 0).testBit q = (decide (q < k) && f q) := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [Finset.sum_range_succ]
    have e : (∑ p ∈ Finset.range k, if f p then 2 ^ p else 0) + (if f k then 2 ^ k else 0)
        = 2 ^ k * (if f k then 1 else 0) + ∑ p ∈ Finset.range k, if f p then 2 ^ p else 0 := by
      split_ifs <;> simp [add_comm]
    rw [e]
    constructor
    · rw [pow_succ]; split_ifs <;> omega
    · intro q
      rw [Nat.testBit_two_pow_mul_add _ h1, h2]
      by_cases hq : q < k
      · simp [hq, Nat.lt_succ_of_lt hq]
      · by_cases hq' : q = k
        · subst hq'; cases f q <;> simp
        · have h3 : (if f k = true then 1 else 0 : ℕ).testBit (q - k) = false := by
            apply Nat.testBit_lt_two_pow
            have : 2 ^ 1 ≤ 2 ^ (q - k) := Nat.pow_le_pow_right (by omega) (by omega)
            split_ifs <;> omega
          rw [ite_eq_right hq, h3]
          have : ¬ q < k + 1 := by omega
          simp [this]

def cbHist (d y t : ℕ) : ℕ := y * 2 ^ d / 2 ^ t

theorem cb_hist_lt (d y t : ℕ) (hy : y < 2 ^ t) : cbHist d y t < 2 ^ d := by
  unfold cbHist
  apply Nat.div_lt_of_lt_mul
  exact Nat.mul_lt_mul_of_lt_of_le hy le_rfl (by positivity)

theorem cb_hist_testBit (d y t k : ℕ) :
    (cbHist d y t).testBit k = (decide (d ≤ k + t) && y.testBit (k + t - d)) := by
  unfold cbHist; rw [Nat.testBit_div_two_pow, Nat.testBit_mul_two_pow]

theorem cb_hist_succ (d y t b : ℕ) :
    cbHist d (2 ^ t * b + y) (t + 1) = (2 ^ d * b + cbHist d y t) / 2 := by
  unfold cbHist
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  congr 1
  rw [add_mul, show 2 ^ t * b * 2 ^ d = 2 ^ t * (2 ^ d * b) by ring, Nat.mul_add_div (by positivity)]

theorem cb_ext_low (t b y j : ℕ) (hy : y < 2 ^ t) (hj : j < t) :
    (2 ^ t * b + y).testBit j = y.testBit j := by
  rw [Nat.testBit_two_pow_mul_add _ hy, ite_eq_left hj]

theorem cb_ext_top (t b y : ℕ) (hy : y < 2 ^ t) :
    (2 ^ t * b + y).testBit t = b.testBit 0 := by
  rw [Nat.testBit_two_pow_mul_add _ hy, ite_eq_right (lt_irrefl t), Nat.sub_self]

theorem cb_v_bit (d t b y k : ℕ) (hy : y < 2 ^ t) (hk : k ≤ d) (hdt : d ≤ t) :
    (2 ^ d * b + cbHist d y t).testBit k = (2 ^ t * b + y).testBit (t - d + k) := by
  rw [Nat.testBit_two_pow_mul_add _ (cb_hist_lt d y t hy), Nat.testBit_two_pow_mul_add _ hy]
  by_cases hkd : k < d
  · rw [ite_eq_left hkd, ite_eq_left (by omega), cb_hist_testBit]
    have h1 : d ≤ k + t := by omega
    have h2 : k + t - d = t - d + k := by omega
    rw [h2]; simp [h1]
  · rw [ite_eq_right hkd, ite_eq_right (by omega)]
    have h1 : k - d = 0 := by omega
    have h2 : t - d + k - t = 0 := by omega
    rw [h1, h2]

theorem cb_posL (n w d i p : ℕ) (hd : d = min w (n - 1)) (hi : i + d < n) (hp : p ≤ w) :
    i ≤ (i + p) % n ∧ (i + p) % n ≤ i + d := by
  rcases le_total w (n - 1) with h | h
  · have h1 : d = w := by omega
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · have h1 : d = n - 1 := by omega
    have h2 : i = 0 := by omega
    subst h2
    have := Nat.mod_lt p (show n > 0 by omega)
    simp only [zero_add]; omega

theorem cb_posW (n m w d i p : ℕ) (hd : d = min w (n - 1)) (hn : 0 < n) (hi : i < m) (hmn : m ≤ n)
    (hid : n ≤ i + d) (hp : p ≤ w) (hq : (i + p) % n < n - d) : (i + p) % n < m + d - n := by
  rcases le_total w (n - 1) with h | h
  · have h1 : d = w := by omega
    by_cases h2 : i + p < n
    · rw [Nat.mod_eq_of_lt h2] at hq ⊢; omega
    · have h3 : (i + p) % n = i + p - n := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [h3]; omega
  · have h1 : d = n - 1 := by omega
    omega

def cbWin (n w z i : ℕ) : ℕ :=
  ∑ p ∈ Finset.range (w + 1), if z.testBit ((i + p) % n) then 2 ^ p else 0

def cbP (n m w d e : ℕ) (T : ℕ → ℕ → Bool) (A : ℕ → Bool → Bool) (t r y : ℕ) : Prop :=
  (∀ j, j < t → A j (y.testBit j) = true) ∧ (∀ j, j < t → j < e → y.testBit j = r.testBit j) ∧
  (∀ i, i < m → i + d < t → T i (cbWin n w y i) = true)

theorem cb_step (n m w d e : ℕ) (T : ℕ → ℕ → Bool) (A : ℕ → Bool → Bool) (t r y b : ℕ)
    (hd : d = min w (n - 1)) (ht : t < n) (hy : y < 2 ^ t) :
    cbP n m w d e T A (t + 1) r (2 ^ t * b + y) ↔
      (cbP n m w d e T A t r y ∧ g n m w d e T A t r (2 ^ d * b + cbHist d y t) = true) := by
  have hv : (2 ^ d * b + cbHist d y t).testBit d = b.testBit 0 := by
    rw [Nat.testBit_two_pow_mul_add _ (cb_hist_lt d y t hy), ite_eq_right (lt_irrefl d), Nat.sub_self]
  have htop := cb_ext_top t b y hy
  have hlow := fun j hj => cb_ext_low t b y j hy hj
  have hwin : ∀ i, i + d < t → cbWin n w (2 ^ t * b + y) i = cbWin n w y i := by
    intro i hi
    unfold cbWin
    apply Finset.sum_congr rfl
    intro p hp
    have := cb_posL n w d i p hd (by omega) (by have := Finset.mem_range.1 hp; omega)
    rw [hlow _ (by omega)]
  have hidx : d ≤ t → idxT n w (t - d) (2 ^ d * b + cbHist d y t)
      = cbWin n w (2 ^ t * b + y) (t - d) := by
    intro hdt
    unfold cbWin idxT
    apply Finset.sum_congr rfl
    intro p hp
    have := cb_posL n w d (t - d) p hd (by omega) (by have := Finset.mem_range.1 hp; omega)
    rw [cb_v_bit d t b y _ hy (by omega) hdt]
    have h2 : t - d + ((t - d + p) % n - (t - d)) = (t - d + p) % n := by omega
    rw [h2]
  unfold g cbP
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, hv]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨fun j hj => ?_, fun j hj hje => ?_, fun i hi hid => ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [← hlow j hj]; exact h1 j (by omega)
    · rw [← hlow j hj]; exact h2 j (by omega) hje
    · rw [← hwin i hid]; exact h3 i hi (by omega)
    · rw [← htop]; exact h1 t (by omega)
    · intro hte; rw [← htop]; exact h2 t (by omega) hte
    · split_ifs with hc
      · rw [hidx hc.1]; exact h3 _ hc.2 (by omega)
      · rfl
  · rintro ⟨⟨h1, h2, h3⟩, ⟨g1, g2⟩, g3⟩
    refine ⟨fun j hj => ?_, fun j hj hje => ?_, fun i hi hid => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [hlow j hj]; exact h1 j hj
      · rw [htop]; exact g1
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [hlow j hj]; exact h2 j hj hje
      · rw [htop]; exact g2 hje
    · by_cases hid' : i + d < t
      · rw [hwin i hid']; exact h3 i hi hid'
      · have hi' : i = t - d := by omega
        have hc : d ≤ t ∧ t - d < m := by omega
        rw [ite_eq_left hc] at g3; subst hi'; rw [← hidx hc.1]; exact g3

theorem cb_regroup (f : ℕ → ℕ) (d H h : ℕ) (hH : H < 2 ^ d) (hh : h < 2 ^ d) :
    (if H / 2 = h then f H else 0) + (if (2 ^ d + H) / 2 = h then f (2 ^ d + H) else 0)
    = (if H = (2 * h) % 2 ^ d then f (2 * h) else 0)
      + (if H = (2 * h + 1) % 2 ^ d then f (2 * h + 1) else 0) := by
  have key : ∀ a b, a = b → f a = f b := fun a b hab => by rw [hab]
  cases d with
  | zero =>
    have h1 : H = 0 := by simpa using hH
    have h2 : h = 0 := by simpa using hh
    subst h1; subst h2; simp
  | succ d =>
    have hK : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ, mul_comm]
    rw [hK] at hH hh ⊢
    generalize 2 ^ d = K at *
    by_cases hc : h < K
    · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      split_ifs <;> first | omega | (simp only [add_zero, zero_add]; apply key; omega)
    · have e0 : (2 * h) % (2 * K) = 2 * h - 2 * K := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      have e1 : (2 * h + 1) % (2 * K) = 2 * h + 1 - 2 * K := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [e0, e1]
      split_ifs <;> first | omega | (simp only [add_zero, zero_add]; apply key; omega)

noncomputable def cbN (n m w d e : ℕ) (T : ℕ → ℕ → Bool) (A : ℕ → Bool → Bool) (t r h : ℕ) : ℕ :=
  ∑ y ∈ Finset.range (2 ^ t), cbInd (cbP n m w d e T A t r y ∧ cbHist d y t = h)

theorem cb_term (n m w d e : ℕ) (T : ℕ → ℕ → Bool) (A : ℕ → Bool → Bool) (t r y b h : ℕ)
    (hd : d = min w (n - 1)) (ht : t < n) (hy : y < 2 ^ t) :
    cbInd (cbP n m w d e T A (t + 1) r (2 ^ t * b + y) ∧ cbHist d (2 ^ t * b + y) (t + 1) = h)
    = cbInd (cbP n m w d e T A t r y) *
      (if (2 ^ d * b + cbHist d y t) / 2 = h then
        (if g n m w d e T A t r (2 ^ d * b + cbHist d y t) then 1 else 0) else 0) := by
  rw [cb_hist_succ, cbInd_and, cbInd_congr (cb_step n m w d e T A t r y b hd ht hy), cbInd_and,
    cbInd_ite (g n m w d e T A t r (2 ^ d * b + cbHist d y t) = true),
    cbInd_ite ((2 ^ d * b + cbHist d y t) / 2 = h), mul_assoc]
  congr 1
  split_ifs <;> simp

theorem cb_lhs (n m w d e : ℕ) (T : ℕ → ℕ → Bool) (A : ℕ → Bool → Bool) (t r v : ℕ) :
    (if g n m w d e T A t r v then cbN n m w d e T A t r (v % 2 ^ d) else 0)
    = ∑ y ∈ Finset.range (2 ^ t), cbInd (cbP n m w d e T A t r y) *
        (if cbHist d y t = v % 2 ^ d then (if g n m w d e T A t r v then 1 else 0) else 0) := by
  unfold cbN
  split_ifs with hg
  · apply Finset.sum_congr rfl
    intro y _
    rw [cbInd_and, cbInd_ite (cbHist d y t = v % 2 ^ d)]
  · simp

theorem cb_count (n m w d e : ℕ) (T : ℕ → ℕ → Bool) (A : ℕ → Bool → Bool) (r : ℕ)
    (hd : d = min w (n - 1)) :
    ∀ t, t ≤ n → ∀ h, h < 2 ^ d → c n m w d e T A t r h = cbN n m w d e T A t r h := by
  intro t
  induction t with
  | zero =>
    intro _ h _
    rw [c]
    unfold cbN
    rw [pow_zero, Finset.sum_range_one, cbInd_and, cbInd_pos, one_mul, cbInd_ite]
    · unfold cbHist; simp [eq_comm]
    · exact ⟨fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega),
        fun i _ hi => absurd hi (by omega)⟩
  | succ t ih =>
    intro ht h hh
    have hpos : 0 < 2 ^ d := by positivity
    rw [c, ih (by omega) _ (Nat.mod_lt _ hpos), ih (by omega) _ (Nat.mod_lt _ hpos), cb_lhs, cb_lhs,
      ← Finset.sum_add_distrib]
    unfold cbN
    rw [show 2 ^ (t + 1) = 2 ^ t + 2 ^ t by rw [pow_succ]; omega, Finset.sum_range_add,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    have hy' := Finset.mem_range.1 hy
    have t0 := cb_term n m w d e T A t r y 0 h hd (by omega) hy'
    have t1 := cb_term n m w d e T A t r y 1 h hd (by omega) hy'
    simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one] at t0 t1
    rw [t0, t1, ← mul_add, ← mul_add]
    congr 1
    exact (cb_regroup (fun v => if g n m w d e T A t r v then 1 else 0) d _ h
      (cb_hist_lt d y t hy') hh).symm

theorem cb_prefix (n e r y : ℕ) (hen : e ≤ n) (hr : r < 2 ^ e) :
    (∀ j, j < n → j < e → y.testBit j = r.testBit j) ↔ r = y % 2 ^ e := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow]
    by_cases hj : j < e
    · rw [h j (by omega) hj]; simp [hj]
    · have : r.testBit j = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hr (Nat.pow_le_pow_right (by omega) (by omega)))
      rw [this]; simp [hj]
  · intro h j _ hj
    rw [h, Nat.testBit_mod_two_pow]; simp [hj]

theorem cb_idxF (n m w d i y : ℕ) (hd : d = min w (n - 1)) (hn : 0 < n) (hi : i < m) (hmn : m ≤ n)
    (hid : n ≤ i + d) :
    idxF n w d i (y % 2 ^ (m + d - n)) (cbHist d y n) = cbWin n w y i := by
  unfold idxF cbWin
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p ≤ w := by have := Finset.mem_range.1 hp; omega
  have hq : (i + p) % n < n := Nat.mod_lt _ hn
  have hdn : d ≤ n - 1 := by omega
  by_cases hc : n - d ≤ (i + p) % n
  · rw [ite_eq_left hc, cb_hist_testBit]
    have h1 : d ≤ (i + p) % n - (n - d) + n := by omega
    have h2 : (i + p) % n - (n - d) + n - d = (i + p) % n := by omega
    rw [h2]; simp [h1]
  · rw [ite_eq_right hc, Nat.testBit_mod_two_pow]
    have := cb_posW n m w d i p hd hn hi hmn hid hp' (by omega)
    simp [this]

theorem cb_F (n m w d : ℕ) (T : ℕ → ℕ → Bool) (r h : ℕ) :
    F n m w d T r h = true ↔ ∀ i, i < m → n ≤ i + d → T i (idxF n w d i r h) = true := by
  unfold F
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]

theorem cb_point (n m w d e : ℕ) (T : ℕ → ℕ → Bool) (A : ℕ → Bool → Bool) (y : ℕ)
    (hd : d = min w (n - 1)) (he : e = m + d - n) (hn : 0 < n) (hmn : m ≤ n) (hy : y < 2 ^ n) :
    (∑ r ∈ Finset.range (2 ^ e), ∑ h ∈ Finset.range (2 ^ d),
      cbInd (F n m w d T r h = true) * cbInd (cbP n m w d e T A n r y ∧ cbHist d y n = h))
    = cbInd ((∀ j, j < n → A j (y.testBit j) = true) ∧
        ∀ i, i < m → T i (cbWin n w y i) = true) := by
  have hpe : 0 < 2 ^ e := by positivity
  have hen : e ≤ n := by omega
  have hH : cbHist d y n < 2 ^ d := cb_hist_lt d y n hy
  rw [Finset.sum_eq_single_of_mem (y % 2 ^ e) (Finset.mem_range.2 (Nat.mod_lt _ hpe)),
    Finset.sum_eq_single_of_mem (cbHist d y n) (Finset.mem_range.2 hH)]
  · rw [← cbInd_and]
    apply cbInd_congr
    rw [cb_F]
    unfold cbP
    constructor
    · rintro ⟨hF, ⟨h1, _, h3⟩, _⟩
      refine ⟨h1, fun i hi => ?_⟩
      by_cases hid : i + d < n
      · exact h3 i hi hid
      · have := hF i hi (by omega)
        rw [he, cb_idxF n m w d i y hd hn hi hmn (by omega)] at this
        exact this
    · rintro ⟨h1, h2⟩
      refine ⟨fun i hi hid => ?_, ⟨h1, ?_, fun i hi _ => h2 i hi⟩, rfl⟩
      · rw [he, cb_idxF n m w d i y hd hn hi hmn hid]; exact h2 i hi
      · exact (cb_prefix n e _ y hen (Nat.mod_lt _ hpe)).2 rfl
  · intro h _ hne
    have h0 : cbInd (cbP n m w d e T A n (y % 2 ^ e) y ∧ cbHist d y n = h) = 0 :=
      cbInd_neg (fun hh => hne hh.2.symm)
    rw [h0, Nat.mul_zero]
  · intro r hr hne
    apply Finset.sum_eq_zero
    intro h _
    have h0 : cbInd (cbP n m w d e T A n r y ∧ cbHist d y n = h) = 0 :=
      cbInd_neg (fun hh => hne ((cb_prefix n e r y hen (Finset.mem_range.1 hr)).1 hh.1.2.1))
    rw [h0, Nat.mul_zero]

theorem cb_final (n m w d e : ℕ) (T : ℕ → ℕ → Bool) (A : ℕ → Bool → Bool)
    (hd : d = min w (n - 1)) (he : e = m + d - n) (hn : 0 < n) (hmn : m ≤ n) :
    (∑ y ∈ Finset.range (2 ^ n), cbInd ((∀ j, j < n → A j (y.testBit j) = true) ∧
        ∀ i, i < m → T i (cbWin n w y i) = true)) = total n m w d e T A := by
  unfold total
  have h1 : ∀ r ∈ Finset.range (2 ^ e), ∀ h ∈ Finset.range (2 ^ d),
      (if F n m w d T r h then c n m w d e T A n r h else 0)
      = ∑ y ∈ Finset.range (2 ^ n),
        cbInd (F n m w d T r h = true) * cbInd (cbP n m w d e T A n r y ∧ cbHist d y n = h) := by
    intro r _ h hh
    rw [cb_count n m w d e T A r hd n le_rfl h (Finset.mem_range.1 hh), ← Finset.mul_sum,
      cbInd_ite]
    unfold cbN
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun r hr => Finset.sum_congr rfl (h1 r hr)),
    Finset.sum_congr rfl (fun r _ => Finset.sum_comm), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  exact (cb_point n m w d e T A y hd he hn hmn (Finset.mem_range.1 hy)).symm

theorem comb : CombStatement := by
  intro n m w hn hm hmn table allow
  rw [← cb_final n m w _ _ _ _ rfl rfl hn hmn, Finset.card_filter,
    ← Fin.sum_univ_eq_sum_range (fun y => cbInd ((∀ j, j < n →
      allow ⟨j % n, Nat.mod_lt _ hn⟩ (y.testBit j) = true) ∧
        ∀ i, i < m → table ⟨i % m, Nat.mod_lt _ hm⟩
          (fun b => (cbWin n w y i).testBit b.val) = true)) (2 ^ n)]
  apply Finset.sum_congr rfl
  intro z _
  have hA : (∀ j : Fin n, allow j (z.val.testBit j.val) = true) ↔
      (∀ j, j < n → allow ⟨j % n, Nat.mod_lt _ hn⟩ (z.val.testBit j) = true) := by
    constructor
    · intro h j hj
      have e : (⟨j % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨j, hj⟩ := Fin.ext (Nat.mod_eq_of_lt hj)
      rw [e]; exact h ⟨j, hj⟩
    · intro h j
      have e : (⟨j.val % n, Nat.mod_lt _ hn⟩ : Fin n) = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
      have := h j.val j.isLt
      rw [e] at this; exact this
  have hW : ∀ i : ℕ, (fun b : Fin (w + 1) => (cbWin n w z.val i).testBit b.val)
      = (fun p : Fin (w + 1) => z.val.testBit ((i + p.val) % n)) := by
    intro i
    funext p
    unfold cbWin
    rw [(cb_bitsum (fun p => z.val.testBit ((i + p) % n)) (w + 1)).2]
    simp [p.isLt]
  have hT : (∀ i : Fin m, table i (fun p => z.val.testBit ((i.val + p.val) % n)) = true) ↔
      (∀ i, i < m → table ⟨i % m, Nat.mod_lt _ hm⟩
          (fun b => (cbWin n w z.val i).testBit b.val) = true) := by
    constructor
    · intro h i hi
      have e : (⟨i % m, Nat.mod_lt _ hm⟩ : Fin m) = ⟨i, hi⟩ := Fin.ext (Nat.mod_eq_of_lt hi)
      rw [e, hW]; exact h ⟨i, hi⟩
    · intro h i
      have e : (⟨i.val % m, Nat.mod_lt _ hm⟩ : Fin m) = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
      have := h i.val i.isLt
      rw [e, hW] at this; exact this
  by_cases hp : (∀ j : Fin n, allow j (z.val.testBit j.val) = true) ∧
      ∀ i : Fin m, table i (fun p => z.val.testBit ((i.val + p.val) % n)) = true
  · rw [ite_eq_left hp, cbInd_pos ⟨hA.1 hp.1, hT.1 hp.2⟩]
  · rw [ite_eq_right hp, cbInd_neg (fun h => hp ⟨hA.2 h.1, hT.2 h.2⟩)]

def val (gs : List Gate) (x : List Bool) (k : ℕ) : Bool :=
  (Circuit.wires ⟨gs, 0⟩ x).getD k false

def OK (N : ℕ) (gs : List Gate) : Prop :=
  PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack N ⟨gs, 0⟩

def Has (N : ℕ) (gs : List Gate) (k : ℕ) (f : List Bool → Bool) : Prop :=
  k < N + gs.length ∧ ∀ x : List Bool, x.length = N → val gs x k = f x

def Ext (N : ℕ) (gs gs' : List Gate) (B : ℕ) : Prop :=
  gs'.length ≤ gs.length + B ∧ (OK N gs → OK N gs') ∧
    ∀ k f, Has N gs k f → Has N gs' k f

theorem Ext.refl' (N : ℕ) (gs : List Gate) : Ext N gs gs 0 :=
  ⟨by simp, id, fun _ _ h => h⟩

theorem Ext.trans' {N : ℕ} {gs1 gs2 gs3 : List Gate} {B1 B2 : ℕ}
    (h1 : Ext N gs1 gs2 B1) (h2 : Ext N gs2 gs3 B2) : Ext N gs1 gs3 (B1 + B2) :=
  ⟨by have := h1.1; have := h2.1; omega, fun h => h2.2.1 (h1.2.1 h),
    fun k f h => h2.2.2 k f (h1.2.2 k f h)⟩

theorem Ext.mono {N : ℕ} {gs gs' : List Gate} {B B' : ℕ}
    (h : Ext N gs gs' B) (hB : B ≤ B') : Ext N gs gs' B' :=
  ⟨by have := h.1; omega, h.2.1, h.2.2⟩

theorem Ext.has {N : ℕ} {gs gs' : List Gate} {B : ℕ} (h : Ext N gs gs' B)
    {k : ℕ} {f : List Bool → Bool} (hk : Has N gs k f) : Has N gs' k f := h.2.2 k f hk

theorem Has.congr {N : ℕ} {gs : List Gate} {k : ℕ} {f f' : List Bool → Bool}
    (h : Has N gs k f) (hf : ∀ x, f x = f' x) : Has N gs k f' :=
  ⟨h.1, fun x hx => (h.2 x hx).trans (hf x)⟩

theorem foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons a l ih => simp only [List.foldl_cons, ih, List.length_append, List.length_cons,
      List.length_nil]; omega

theorem wires_length (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := foldl_len gs x

theorem wires_snoc (gs : List Gate) (gt : Gate) (x : List Bool) :
    Circuit.wires ⟨gs ++ [gt], 0⟩ x = Circuit.wires ⟨gs, 0⟩ x ++
      [gt.op.eval (gt.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

theorem ext_snoc (N : ℕ) (gs : List Gate) (gt : Gate)
    (hop : gt.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : gt.inputs.length ≤ 2) (hin : ∀ i ∈ gt.inputs, i < N + gs.length) :
    Ext N gs (gs ++ [gt]) 1 ∧ ∀ x : List Bool, x.length = N →
      val (gs ++ [gt]) x (N + gs.length) = gt.op.eval (gt.inputs.map fun i => val gs x i) := by
  refine ⟨⟨by simp, ?_, ?_⟩, ?_⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro g' hg'
      have hg2 : g' ∈ gs ∨ g' = gt := by simpa using hg'
      rcases hg2 with h | h
      · exact h1 g' h
      · subst h; exact ⟨hop, hlen⟩
    · intro j hj i hi
      have hj1 : j < gs.length + 1 := by simpa using hj
      by_cases hj' : j < gs.length
      · have e1 : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs ++ [gt], 0⟩ j =
            PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, 0⟩ j := by
          simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getElem?_append_left hj']
        rw [e1] at hi
        exact h2 j hj' i hi
      · have hj2 : j = gs.length := by omega
        subst hj2
        have e1 : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs ++ [gt], 0⟩ gs.length = gt := by
          simp [PEqualNP.MetaComplexity.NestedCover.gateAt]
        rw [e1] at hi
        exact hin i hi
  · intro k f ⟨hk, hf⟩
    refine ⟨by simp; omega, fun x hx => ?_⟩
    rw [← hf x hx]
    unfold val
    rw [wires_snoc]
    exact List.getD_append _ _ _ _ (by rw [wires_length]; omega)
  · intro x hx
    unfold val
    rw [wires_snoc, List.getD_append_right _ _ _ _ (by rw [wires_length]; omega), wires_length]
    simp [hx]

theorem has_and {N : ℕ} {gs : List Gate} {ka kb : ℕ} {fa fb : List Bool → Bool}
    (ha : Has N gs ka fa) (hb : Has N gs kb fb) :
    ∃ gs' k, Ext N gs gs' 1 ∧ Has N gs' k (fun x => fa x && fb x) := by
  obtain ⟨hE, hv⟩ := ext_snoc N gs ⟨GateOp.and, [ka, kb]⟩ (by simp) (by simp)
    (by intro i hi; simp at hi; rcases hi with rfl | rfl; exact ha.1; exact hb.1)
  refine ⟨_, N + gs.length, hE, by simp, fun x hx => ?_⟩
  rw [hv x hx]; simp [GateOp.eval, ha.2 x hx, hb.2 x hx]

theorem has_or {N : ℕ} {gs : List Gate} {ka kb : ℕ} {fa fb : List Bool → Bool}
    (ha : Has N gs ka fa) (hb : Has N gs kb fb) :
    ∃ gs' k, Ext N gs gs' 1 ∧ Has N gs' k (fun x => fa x || fb x) := by
  obtain ⟨hE, hv⟩ := ext_snoc N gs ⟨GateOp.or, [ka, kb]⟩ (by simp) (by simp)
    (by intro i hi; simp at hi; rcases hi with rfl | rfl; exact ha.1; exact hb.1)
  refine ⟨_, N + gs.length, hE, by simp, fun x hx => ?_⟩
  rw [hv x hx]; simp [GateOp.eval, ha.2 x hx, hb.2 x hx]

theorem has_not {N : ℕ} {gs : List Gate} {ka : ℕ} {fa : List Bool → Bool}
    (ha : Has N gs ka fa) :
    ∃ gs' k, Ext N gs gs' 1 ∧ Has N gs' k (fun x => !fa x) := by
  obtain ⟨hE, hv⟩ := ext_snoc N gs ⟨GateOp.not, [ka]⟩ (by simp) (by simp)
    (by intro i hi; simp at hi; subst hi; exact ha.1)
  refine ⟨_, N + gs.length, hE, by simp, fun x hx => ?_⟩
  rw [hv x hx]; simp [GateOp.eval, ha.2 x hx]

theorem has_false (N : ℕ) (gs : List Gate) :
    ∃ gs' k, Ext N gs gs' 1 ∧ Has N gs' k (fun _ => false) := by
  obtain ⟨hE, hv⟩ := ext_snoc N gs ⟨GateOp.or, []⟩ (by simp) (by simp) (by simp)
  refine ⟨_, N + gs.length, hE, by simp, fun x hx => ?_⟩
  rw [hv x hx]; simp [GateOp.eval]

theorem has_true (N : ℕ) (gs : List Gate) :
    ∃ gs' k, Ext N gs gs' 1 ∧ Has N gs' k (fun _ => true) := by
  obtain ⟨hE, hv⟩ := ext_snoc N gs ⟨GateOp.and, []⟩ (by simp) (by simp) (by simp)
  refine ⟨_, N + gs.length, hE, by simp, fun x hx => ?_⟩
  rw [hv x hx]; simp [GateOp.eval]

theorem chain (N K B : ℕ) (Q : ℕ → List Gate → Prop) (gs0 : List Gate) (h0 : Q 0 gs0)
    (step : ∀ k < K, ∀ gs', Ext N gs0 gs' (k * B) → Q k gs' →
      ∃ gs'', Ext N gs' gs'' B ∧ Q (k + 1) gs'') :
    ∃ gs', Ext N gs0 gs' (K * B) ∧ Q K gs' := by
  induction K with
  | zero => exact ⟨gs0, by simpa using Ext.refl' N gs0, h0⟩
  | succ K ih =>
    obtain ⟨gs1, h1, q1⟩ := ih (fun k hk => step k (by omega))
    obtain ⟨gs2, h2, q2⟩ := step K (by omega) gs1 h1 q1
    exact ⟨gs2, by rw [Nat.succ_mul]; exact h1.trans' h2, q2⟩

def Vec (N : ℕ) (gs : List Gate) (L : ℕ) (a : List Bool → ℕ) : Prop :=
  ∀ i < L, ∃ k, Has N gs k (fun x => (a x).testBit i)

theorem Ext.vec {N : ℕ} {gs gs' : List Gate} {B : ℕ} (h : Ext N gs gs' B)
    {L : ℕ} {a : List Bool → ℕ} (hv : Vec N gs L a) : Vec N gs' L a :=
  fun i hi => let ⟨k, hk⟩ := hv i hi; ⟨k, h.has hk⟩

theorem Vec.congr {N : ℕ} {gs : List Gate} {L : ℕ} {a a' : List Bool → ℕ}
    (hv : Vec N gs L a) (ha : ∀ x, a x = a' x) : Vec N gs L a' :=
  fun i hi => let ⟨k, hk⟩ := hv i hi; ⟨k, hk.congr (fun x => by rw [ha x])⟩

def Base (N : ℕ) (gs : List Gate) : Prop :=
  (∀ k < N, Has N gs k (fun x => x.getD k false)) ∧ ∀ b : Bool, ∃ k, Has N gs k (fun _ => b)

theorem Ext.base {N : ℕ} {gs gs' : List Gate} {B : ℕ} (h : Ext N gs gs' B)
    (hb : Base N gs) : Base N gs' :=
  ⟨fun k hk => h.has (hb.1 k hk), fun b => let ⟨k, hk⟩ := hb.2 b; ⟨k, h.has hk⟩⟩

theorem ok_nil (N : ℕ) : OK N [] := by
  refine ⟨?_, ?_⟩
  · intro g' hg'; simp at hg'
  · intro j hj; simp at hj

theorem base_exists (N : ℕ) : ∃ gs, Ext N [] gs 2 ∧ Base N gs := by
  obtain ⟨g1, k1, E1, H1⟩ := has_false N []
  obtain ⟨g2, k2, E2, H2⟩ := has_true N g1
  refine ⟨g2, E1.trans' E2, ?_, ?_⟩
  · intro k hk
    refine (E1.trans' E2).has ⟨by simpa using hk, fun x _ => rfl⟩
  · intro b
    cases b
    · exact ⟨k1, E2.has H1⟩
    · exact ⟨k2, H2⟩

theorem vec_const {N : ℕ} {gs : List Gate} (hb : Base N gs) (L a : ℕ) :
    Vec N gs L (fun _ => a) := fun i _ => hb.2 (a.testBit i)

def cry (i a b : ℕ) : Bool := decide (2 ^ i ≤ a % 2 ^ i + b % 2 ^ i)

theorem cry_zero (a b : ℕ) : cry 0 a b = false := by
  simp [cry, Nat.mod_one]

theorem cry_succ (i a b : ℕ) :
    cry (i + 1) a b = (a.testBit i && b.testBit i || (a.testBit i ^^ b.testBit i) && cry i a b) := by
  unfold cry
  have ea : a % 2 ^ (i + 1) = a % 2 ^ i + 2 ^ i * (a.testBit i).toNat := by
    rw [Nat.mod_pow_succ, Nat.toNat_testBit]
  have eb : b % 2 ^ (i + 1) = b % 2 ^ i + 2 ^ i * (b.testBit i).toNat := by
    rw [Nat.mod_pow_succ, Nat.toNat_testBit]
  rw [ea, eb, pow_succ]
  have ha : a % 2 ^ i < 2 ^ i := Nat.mod_lt _ (by positivity)
  have hb : b % 2 ^ i < 2 ^ i := Nat.mod_lt _ (by positivity)
  generalize a % 2 ^ i = u at *
  generalize b % 2 ^ i = v at *
  generalize 2 ^ i = P at *
  cases a.testBit i <;> cases b.testBit i <;> simp <;> omega

theorem testBit_add_cry (i a b : ℕ) :
    (a + b).testBit i = (a.testBit i ^^ (b.testBit i ^^ cry i a b)) := by
  have h1 : (a + b).testBit i = (BitVec.ofNat (i + 1) (a + b)).getLsbD i := by
    rw [BitVec.getLsbD_ofNat]; simp
  rw [h1, BitVec.ofNat_add, BitVec.getLsbD_add (by omega)]
  simp only [BitVec.getLsbD_ofNat, BitVec.carry, BitVec.toNat_ofNat]
  have e1 : ∀ z : ℕ, z % 2 ^ (i + 1) % 2 ^ i = z % 2 ^ i := fun z =>
    Nat.mod_mod_of_dvd z (pow_dvd_pow 2 (Nat.le_succ i))
  simp [e1, cry]

theorem has_xor {N : ℕ} {gs : List Gate} {ka kb : ℕ} {fa fb : List Bool → Bool}
    (ha : Has N gs ka fa) (hb : Has N gs kb fb) :
    ∃ gs' kx kd, Ext N gs gs' 4 ∧ Has N gs' kx (fun x => fa x ^^ fb x) ∧
      Has N gs' kd (fun x => fa x && fb x) := by
  obtain ⟨g1, k1, E1, H1⟩ := has_or ha hb
  obtain ⟨g2, k2, E2, H2⟩ := has_and (E1.has ha) (E1.has hb)
  obtain ⟨g3, k3, E3, H3⟩ := has_not H2
  obtain ⟨g4, k4, E4, H4⟩ := has_and (E3.has (E2.has H1)) H3
  refine ⟨g4, k4, k2, ((E1.trans' E2).trans' E3).trans' E4, H4.congr ?_, E4.has (E3.has H2)⟩
  intro x; cases fa x <;> cases fb x <;> rfl

theorem has_fa {N : ℕ} {gs : List Gate} {ka kb kc : ℕ} {fa fb fc : List Bool → Bool}
    (ha : Has N gs ka fa) (hb : Has N gs kb fb) (hc : Has N gs kc fc) :
    ∃ gs' ks kc', Ext N gs gs' 9 ∧ Has N gs' ks (fun x => fa x ^^ (fb x ^^ fc x)) ∧
      Has N gs' kc' (fun x => fa x && fb x || (fa x ^^ fb x) && fc x) := by
  obtain ⟨g1, kx, kd, E1, Hx, Hd⟩ := has_xor ha hb
  obtain ⟨g2, ks, kd2, E2, Hs, Hd2⟩ := has_xor Hx (E1.has hc)
  obtain ⟨g3, ko, E3, Ho⟩ := has_or (E2.has Hd) Hd2
  refine ⟨g3, ks, ko, (E1.trans' E2).trans' E3, (E3.has Hs).congr ?_, Ho⟩
  intro x; cases fa x <;> cases fb x <;> cases fc x <;> rfl

theorem vec_add {N : ℕ} {gs : List Gate} {L : ℕ} {a b : List Bool → ℕ}
    (hb0 : Base N gs) (ha : Vec N gs L a) (hb : Vec N gs L b) :
    ∃ gs', Ext N gs gs' (L * 9) ∧ Vec N gs' L (fun x => a x + b x) := by
  obtain ⟨gs', hE, hQ, -⟩ := chain N L 9
    (fun i gs' => (∀ j < i, ∃ k, Has N gs' k (fun x => (a x + b x).testBit j)) ∧
      ∃ kc, Has N gs' kc (fun x => cry i (a x) (b x))) gs
    ⟨fun j hj => absurd hj (Nat.not_lt_zero j), by
      obtain ⟨k, hk⟩ := hb0.2 false
      exact ⟨k, hk.congr (fun x => (cry_zero _ _).symm)⟩⟩
    (by
      intro i hi gs1 E1 ⟨Q1, kc, Hc⟩
      obtain ⟨ka, Ha⟩ := ha i hi
      obtain ⟨kb, Hb⟩ := hb i hi
      obtain ⟨gs2, ks, kc', E2, Hs, Hc'⟩ := has_fa (E1.has Ha) (E1.has Hb) Hc
      refine ⟨gs2, E2, ?_, kc', Hc'.congr (fun x => (cry_succ _ _ _).symm)⟩
      intro j hj
      by_cases hj' : j < i
      · obtain ⟨k, hk⟩ := Q1 j hj'
        exact ⟨k, E2.has hk⟩
      · have : j = i := by omega
        subst this
        exact ⟨ks, Hs.congr (fun x => (testBit_add_cry _ _ _).symm)⟩)
  exact ⟨gs', hE, hQ⟩

theorem vec_mask {N : ℕ} {gs : List Gate} {L : ℕ} {a : List Bool → ℕ} {kp : ℕ}
    {p : List Bool → Bool} (hp : Has N gs kp p) (ha : Vec N gs L a) :
    ∃ gs', Ext N gs gs' (L * 1) ∧ Vec N gs' L (fun x => if p x then a x else 0) := by
  obtain ⟨gs', hE, hQ⟩ := chain N L 1
    (fun i gs' => ∀ j < i, ∃ k, Has N gs' k (fun x => (if p x then a x else 0).testBit j)) gs
    (fun j hj => absurd hj (Nat.not_lt_zero j))
    (by
      intro i hi gs1 E1 Q1
      obtain ⟨ka, Ha⟩ := ha i hi
      obtain ⟨gs2, k2, E2, H2⟩ := has_and (E1.has hp) (E1.has Ha)
      refine ⟨gs2, E2, ?_⟩
      intro j hj
      by_cases hj' : j < i
      · obtain ⟨k, hk⟩ := Q1 j hj'
        exact ⟨k, E2.has hk⟩
      · have : j = i := by omega
        subst this
        refine ⟨k2, H2.congr (fun x => ?_)⟩
        cases p x <;> simp)
  exact ⟨gs', hE, hQ⟩

def Tx (w : ℕ) (x : List Bool) (i a : ℕ) : Bool := x.getD (i * 2 ^ (w + 1) + a) false

def Ax (m w : ℕ) (x : List Bool) (j : ℕ) (b : Bool) : Bool :=
  x.getD (m * 2 ^ (w + 1) + 2 * j + (if b then 1 else 0)) false

theorem sum_pow_lt (L : ℕ) (b : ℕ → Bool) :
    (∑ p ∈ Finset.range L, if b p then 2 ^ p else 0) < 2 ^ L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, pow_succ]
    split <;> omega

theorem idxT_lt (n w i v : ℕ) : idxT n w i v < 2 ^ (w + 1) :=
  sum_pow_lt (w + 1) (fun p => v.testBit ((i + p) % n - i))

theorem idxF_lt (n w d i r h : ℕ) : idxF n w d i r h < 2 ^ (w + 1) :=
  sum_pow_lt (w + 1) (fun p =>
    if n - d ≤ (i + p) % n then h.testBit ((i + p) % n - (n - d)) else r.testBit ((i + p) % n))

theorem tbl_lt (n m W i a : ℕ) (hi : i < m) (ha : a < W) : i * W + a < m * W + 2 * n := by
  have h1 := Nat.mul_le_mul_right W (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at h1
  omega

theorem guard_has {n m w d e : ℕ} {gs : List Gate} (hb : Base (m * 2 ^ (w + 1) + 2 * n) gs)
    {t : ℕ} (ht : t < n) (r v : ℕ) :
    ∃ gs' k, Ext (m * 2 ^ (w + 1) + 2 * n) gs gs' 2 ∧
      Has (m * 2 ^ (w + 1) + 2 * n) gs' k (fun x => g n m w d e (Tx w x) (Ax m w x) t r v) := by
  have hA : Has (m * 2 ^ (w + 1) + 2 * n) gs
      (m * 2 ^ (w + 1) + 2 * t + (if v.testBit d then 1 else 0))
      (fun x => Ax m w x t (v.testBit d)) :=
    hb.1 _ (by split <;> omega)
  obtain ⟨kS, hS⟩ := hb.2 (decide (t < e → v.testBit d = r.testBit t))
  have h3 : ∃ k3, Has (m * 2 ^ (w + 1) + 2 * n) gs k3
      (fun x => if d ≤ t ∧ t - d < m then Tx w x (t - d) (idxT n w (t - d) v) else true) := by
    by_cases hc : d ≤ t ∧ t - d < m
    · refine ⟨(t - d) * 2 ^ (w + 1) + idxT n w (t - d) v, ?_⟩
      simp only [hc, and_self, ↓reduceIte]
      exact hb.1 _ (tbl_lt n m _ _ _ hc.2 (idxT_lt _ _ _ _))
    · simp only [hc, ↓reduceIte]
      exact hb.2 true
  obtain ⟨k3, h3⟩ := h3
  obtain ⟨g1, k1, E1, H1⟩ := has_and hA hS
  obtain ⟨g2, k2, E2, H2⟩ := has_and H1 (E1.has h3)
  exact ⟨g2, k2, E1.trans' E2, H2⟩

def Lev (n m w d e t : ℕ) (gs : List Gate) : Prop :=
  ∀ r < 2 ^ e, ∀ h < 2 ^ d, Vec (m * 2 ^ (w + 1) + 2 * n) gs (n + 1)
    (fun x => c n m w d e (Tx w x) (Ax m w x) t r h)

theorem Ext.lev {n m w d e t : ℕ} {gs gs' : List Gate} {B : ℕ}
    (h : Ext (m * 2 ^ (w + 1) + 2 * n) gs gs' B) (hl : Lev n m w d e t gs) :
    Lev n m w d e t gs' := fun r hr h' hh => h.vec (hl r hr h' hh)

theorem state_step {n m w d e : ℕ} {gs : List Gate} (hb : Base (m * 2 ^ (w + 1) + 2 * n) gs)
    {t : ℕ} (ht : t < n) (hl : Lev n m w d e t gs) (r h : ℕ) (hr : r < 2 ^ e) :
    ∃ gs', Ext (m * 2 ^ (w + 1) + 2 * n) gs gs' (11 * (n + 1) + 4) ∧
      Vec (m * 2 ^ (w + 1) + 2 * n) gs' (n + 1)
        (fun x => c n m w d e (Tx w x) (Ax m w x) (t + 1) r h) := by
  have hd : 0 < 2 ^ d := by positivity
  obtain ⟨g1, k1, E1, H1⟩ := guard_has (d := d) (e := e) hb ht r (2 * h)
  obtain ⟨g2, E2, V2⟩ := vec_mask H1 (E1.vec (hl r hr ((2 * h) % 2 ^ d) (Nat.mod_lt _ hd)))
  obtain ⟨g3, k3, E3, H3⟩ := guard_has (d := d) (e := e) ((E1.trans' E2).base hb) ht r (2 * h + 1)
  obtain ⟨g4, E4, V4⟩ := vec_mask H3
    (((E1.trans' E2).trans' E3).vec (hl r hr ((2 * h + 1) % 2 ^ d) (Nat.mod_lt _ hd)))
  obtain ⟨g5, E5, V5⟩ := vec_add ((((E1.trans' E2).trans' E3).trans' E4).base hb)
    ((E3.trans' E4).vec V2) V4
  refine ⟨g5, (((((E1.trans' E2).trans' E3).trans' E4).trans' E5)).mono (by omega), ?_⟩
  exact V5.congr (fun x => by simp only [c])

theorem div_mod_idx (D r h : ℕ) (hh : h < D) : (r * D + h) / D = r ∧ (r * D + h) % D = h := by
  have hD : 0 < D := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt hh, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hh]

theorem level_step {n m w d e : ℕ} {gs : List Gate} (hb : Base (m * 2 ^ (w + 1) + 2 * n) gs)
    {t : ℕ} (ht : t < n) (hl : Lev n m w d e t gs) :
    ∃ gs', Ext (m * 2 ^ (w + 1) + 2 * n) gs gs' (2 ^ e * 2 ^ d * (11 * (n + 1) + 4)) ∧
      Lev n m w d e (t + 1) gs' := by
  have hd : 0 < 2 ^ d := by positivity
  obtain ⟨gs', hE, hQ⟩ := chain (m * 2 ^ (w + 1) + 2 * n) (2 ^ e * 2 ^ d) (11 * (n + 1) + 4)
    (fun k gs' => ∀ j < k, Vec (m * 2 ^ (w + 1) + 2 * n) gs' (n + 1)
      (fun x => c n m w d e (Tx w x) (Ax m w x) (t + 1) (j / 2 ^ d) (j % 2 ^ d))) gs
    (fun j hj => absurd hj (Nat.not_lt_zero j))
    (by
      intro k hk gs1 E1 Q1
      obtain ⟨gs2, E2, V2⟩ := state_step (E1.base hb) ht (E1.lev hl) (k / 2 ^ d) (k % 2 ^ d)
        (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk))
      refine ⟨gs2, E2, ?_⟩
      intro j hj
      by_cases hj' : j < k
      · exact E2.vec (Q1 j hj')
      · have : j = k := by omega
        subst this
        exact V2)
  refine ⟨gs', hE, ?_⟩
  intro r hr h hh
  have h1 := div_mod_idx (2 ^ d) r h hh
  have h2 : r * 2 ^ d + h < 2 ^ e * 2 ^ d := by
    have := Nat.mul_le_mul_right (2 ^ d) (Nat.succ_le_of_lt hr)
    rw [Nat.succ_mul] at this
    omega
  have h3 := hQ _ h2
  rw [h1.1, h1.2] at h3
  exact h3

theorem levels {n m w d e : ℕ} {gs : List Gate} (hb : Base (m * 2 ^ (w + 1) + 2 * n) gs) :
    ∃ gs', Ext (m * 2 ^ (w + 1) + 2 * n) gs gs' (n * (2 ^ e * 2 ^ d * (11 * (n + 1) + 4))) ∧
      Lev n m w d e n gs' := by
  refine chain (m * 2 ^ (w + 1) + 2 * n) n (2 ^ e * 2 ^ d * (11 * (n + 1) + 4))
    (fun t gs' => Lev n m w d e t gs') gs ?_ ?_
  · intro r _ h _
    exact (vec_const hb (n + 1) (if h = 0 then 1 else 0)).congr (fun x => by simp only [c])
  · intro t ht gs1 E1 Q1
    exact level_step (E1.base hb) ht Q1

def Fq (n w d : ℕ) (T : ℕ → ℕ → Bool) (r h : ℕ) (i : ℕ) : Bool :=
  decide (n ≤ i + d) → T i (idxF n w d i r h)

theorem F_eq (n m w d : ℕ) (T : ℕ → ℕ → Bool) (r h : ℕ) :
    F n m w d T r h = (List.range m).all (Fq n w d T r h) := rfl

theorem F_has {n m w d : ℕ} {gs : List Gate} (hb : Base (m * 2 ^ (w + 1) + 2 * n) gs)
    (r h : ℕ) :
    ∃ gs' k, Ext (m * 2 ^ (w + 1) + 2 * n) gs gs' (m * 1) ∧
      Has (m * 2 ^ (w + 1) + 2 * n) gs' k (fun x => F n m w d (Tx w x) r h) := by
  have key : ∀ M ≤ m, ∃ gs', Ext (m * 2 ^ (w + 1) + 2 * n) gs gs' (M * 1) ∧
      ∃ k, Has (m * 2 ^ (w + 1) + 2 * n) gs' k
        (fun x => (List.range M).all (Fq n w d (Tx w x) r h)) := by
    intro M hM
    refine chain (m * 2 ^ (w + 1) + 2 * n) M 1
      (fun i gs' => ∃ k, Has (m * 2 ^ (w + 1) + 2 * n) gs' k
        (fun x => (List.range i).all (Fq n w d (Tx w x) r h))) gs ?_ ?_
    · obtain ⟨k, hk⟩ := hb.2 true
      exact ⟨k, hk.congr (fun x => by simp)⟩
    · intro i hi gs1 E1 ⟨k1, H1⟩
      by_cases hs : n ≤ i + d
      · have hT : Has (m * 2 ^ (w + 1) + 2 * n) gs1 (i * 2 ^ (w + 1) + idxF n w d i r h)
            (fun x => Tx w x i (idxF n w d i r h)) :=
          E1.has (hb.1 _ (tbl_lt n m _ _ _ (by omega) (idxF_lt _ _ _ _ _ _)))
        obtain ⟨gs2, k2, E2, H2⟩ := has_and H1 hT
        refine ⟨gs2, E2, k2, H2.congr (fun x => ?_)⟩
        simp [List.range_succ, Fq, hs]
      · refine ⟨gs1, (Ext.refl' _ gs1).mono (by omega), k1, H1.congr (fun x => ?_)⟩
        simp [List.range_succ, Fq, hs]
  obtain ⟨gs', hE, k, hk⟩ := key m le_rfl
  exact ⟨gs', k, hE, hk⟩

def term (n m w d e : ℕ) (x : List Bool) (j : ℕ) : ℕ :=
  if F n m w d (Tx w x) (j / 2 ^ d) (j % 2 ^ d)
  then c n m w d e (Tx w x) (Ax m w x) n (j / 2 ^ d) (j % 2 ^ d) else 0

theorem acc {n m w d e : ℕ} {gs : List Gate} (hb : Base (m * 2 ^ (w + 1) + 2 * n) gs)
    (hl : Lev n m w d e n gs) :
    ∃ gs', Ext (m * 2 ^ (w + 1) + 2 * n) gs gs' (2 ^ e * 2 ^ d * (m + 10 * (n + 1))) ∧
      Vec (m * 2 ^ (w + 1) + 2 * n) gs' (n + 1)
        (fun x => ∑ j ∈ Finset.range (2 ^ e * 2 ^ d), term n m w d e x j) := by
  have hd : 0 < 2 ^ d := by positivity
  refine chain (m * 2 ^ (w + 1) + 2 * n) (2 ^ e * 2 ^ d) (m + 10 * (n + 1))
    (fun k gs' => Vec (m * 2 ^ (w + 1) + 2 * n) gs' (n + 1)
      (fun x => ∑ j ∈ Finset.range k, term n m w d e x j)) gs ?_ ?_
  · exact (vec_const hb (n + 1) 0).congr (fun x => by simp)
  · intro k hk gs1 E1 Q1
    obtain ⟨g2, kF, E2, HF⟩ := F_has (n := n) (d := d) (E1.base hb) (k / 2 ^ d) (k % 2 ^ d)
    obtain ⟨g3, E3, V3⟩ := vec_mask HF ((E1.trans' E2).vec (hl (k / 2 ^ d)
      (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk)) (k % 2 ^ d) (Nat.mod_lt _ hd)))
    obtain ⟨g4, E4, V4⟩ := vec_add (((E1.trans' E2).trans' E3).base hb)
      ((E2.trans' E3).vec Q1) V3
    refine ⟨g4, ((E2.trans' E3).trans' E4).mono (by omega), V4.congr (fun x => ?_)⟩
    rw [Finset.sum_range_succ]; rfl

theorem sum_div_mod (R H : ℕ) (_hH : 0 < H) (f : ℕ → ℕ → ℕ) :
    ∑ r ∈ Finset.range R, ∑ h ∈ Finset.range H, f r h =
      ∑ k ∈ Finset.range (R * H), f (k / H) (k % H) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ, ih, Nat.succ_mul, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl (fun h hh => ?_)
    have := div_mod_idx H R h (Finset.mem_range.mp hh)
    rw [this.1, this.2]

theorem total_eq (n m w d e : ℕ) (x : List Bool) :
    total n m w d e (Tx w x) (Ax m w x) =
      ∑ j ∈ Finset.range (2 ^ e * 2 ^ d), term n m w d e x j := by
  unfold total
  rw [sum_div_mod (2 ^ e) (2 ^ d) (by positivity)]
  rfl

theorem g_congr {n m w d e : ℕ} {T T' : ℕ → ℕ → Bool} {A A' : ℕ → Bool → Bool}
    (hT : ∀ i < m, ∀ a < 2 ^ (w + 1), T i a = T' i a) (hA : ∀ j < n, ∀ b, A j b = A' j b)
    {t : ℕ} (ht : t < n) (r v : ℕ) : g n m w d e T A t r v = g n m w d e T' A' t r v := by
  unfold g
  rw [hA t ht]
  congr 1
  split_ifs with hc
  · exact hT _ hc.2 _ (idxT_lt _ _ _ _)
  · rfl

theorem c_congr {n m w d e : ℕ} {T T' : ℕ → ℕ → Bool} {A A' : ℕ → Bool → Bool}
    (hT : ∀ i < m, ∀ a < 2 ^ (w + 1), T i a = T' i a) (hA : ∀ j < n, ∀ b, A j b = A' j b)
    (t : ℕ) (ht : t ≤ n) (r h : ℕ) : c n m w d e T A t r h = c n m w d e T' A' t r h := by
  induction t generalizing h with
  | zero => simp only [c]
  | succ t ih =>
    simp only [c]
    rw [g_congr hT hA (by omega), g_congr hT hA (by omega), ih (by omega), ih (by omega)]

theorem F_congr {n m w d : ℕ} {T T' : ℕ → ℕ → Bool}
    (hT : ∀ i < m, ∀ a < 2 ^ (w + 1), T i a = T' i a) (r h : ℕ) :
    F n m w d T r h = F n m w d T' r h := by
  rw [F_eq, F_eq, Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_range]
  have e1 : ∀ i < m, Fq n w d T r h i = Fq n w d T' r h i := by
    intro i hi
    unfold Fq
    rw [hT i hi _ (idxF_lt _ _ _ _ _ _)]
  constructor
  · intro H i hi; rw [← e1 i hi]; exact H i hi
  · intro H i hi; rw [e1 i hi]; exact H i hi

theorem total_congr {n m w d e : ℕ} {T T' : ℕ → ℕ → Bool} {A A' : ℕ → Bool → Bool}
    (hT : ∀ i < m, ∀ a < 2 ^ (w + 1), T i a = T' i a) (hA : ∀ j < n, ∀ b, A j b = A' j b) :
    total n m w d e T A = total n m w d e T' A' := by
  unfold total
  refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun h _ => ?_))
  rw [F_congr hT, c_congr hT hA n le_rfl]

theorem circ_le : ∀ (n m w d e : ℕ), 0 < n → 0 < m → m ≤ n →
    ∃ (C : Circuit) (outBit : Fin (n + 1) → ℕ),
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (m * 2 ^ (w + 1) + 2 * n) C ∧
      C.size ≤ 16 * (n + 1) ^ 2 * 2 ^ (d + e) + 2 ∧
      C.output = outBit 0 ∧ (∀ j, outBit j < m * 2 ^ (w + 1) + 2 * n + C.size) ∧
      ∀ (T : ℕ → ℕ → Bool) (A : ℕ → Bool → Bool) (x : List Bool),
        x.length = m * 2 ^ (w + 1) + 2 * n →
        (∀ i < m, ∀ a < 2 ^ (w + 1), x.getD (i * 2 ^ (w + 1) + a) false = T i a) →
        (∀ j < n, ∀ b : Bool, x.getD (m * 2 ^ (w + 1) + 2 * j + (if b then 1 else 0)) false = A j b) →
        ∀ b : Fin (n + 1),
          (C.wires x).getD (outBit b) false = (total n m w d e T A % 2 ^ (n + 1)).testBit b.val := by
  intro n m w d e _ _ hmn
  obtain ⟨g0, E0, hb0⟩ := base_exists (m * 2 ^ (w + 1) + 2 * n)
  obtain ⟨g1, E1, hl⟩ := levels (d := d) (e := e) hb0
  obtain ⟨g2, E2, hv⟩ := acc (E1.base hb0) hl
  have E := (E0.trans' E1).trans' E2
  have hok := E.2.1 (ok_nil _)
  have hsz : g2.length ≤ 16 * (n + 1) ^ 2 * 2 ^ (d + e) + 2 := by
    have h1 := E.1
    have h2 : n * (2 ^ e * 2 ^ d * (11 * (n + 1) + 4)) + 2 ^ e * 2 ^ d * (m + 10 * (n + 1))
        ≤ 16 * (n + 1) ^ 2 * 2 ^ (d + e) := by
      have h3 : 2 ^ (d + e) = 2 ^ e * 2 ^ d := by rw [Nat.add_comm, pow_add]
      rw [h3]
      generalize 2 ^ e * 2 ^ d = S
      have h4 : n * (11 * (n + 1) + 4) + (m + 10 * (n + 1)) ≤ 16 * (n + 1) ^ 2 := by nlinarith
      calc n * (S * (11 * (n + 1) + 4)) + S * (m + 10 * (n + 1))
          = S * (n * (11 * (n + 1) + 4) + (m + 10 * (n + 1))) := by ring
        _ ≤ S * (16 * (n + 1) ^ 2) := Nat.mul_le_mul_left S h4
        _ = 16 * (n + 1) ^ 2 * S := by ring
    simp only [List.length_nil] at h1
    omega
  choose! ks hks using hv
  refine ⟨⟨g2, ks 0⟩, fun j => ks j.val, hok.1, hok.2, hsz, rfl, fun j => (hks j.val j.isLt).1, ?_⟩
  intro T A x hx hT hA b
  have h1 : (Circuit.wires ⟨g2, ks 0⟩ x).getD (ks b.val) false = val g2 x (ks b.val) := rfl
  rw [h1, (hks b.val b.isLt).2 x hx]
  beta_reduce
  rw [← total_eq, Nat.testBit_mod_two_pow]
  have h2 : total n m w d e (Tx w x) (Ax m w x) = total n m w d e T A :=
    total_congr (fun i hi a ha => hT i hi a ha) (fun j hj b' => hA j hj b')
  rw [h2]
  simp [b.isLt]

def CircStatementLe : Prop :=
  ∀ (n m w d e : ℕ), 0 < n → 0 < m → m ≤ n →
      ∃ (C : Circuit) (outBit : Fin (n + 1) → ℕ),
        PEqualNP.MetaComplexity.FanInTwo C ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (m * 2 ^ (w + 1) + 2 * n) C ∧
        C.size ≤ 16 * (n + 1) ^ 2 * 2 ^ (d + e) + 2 ∧
        C.output = outBit 0 ∧ (∀ j, outBit j < m * 2 ^ (w + 1) + 2 * n + C.size) ∧
        ∀ (T : ℕ → ℕ → Bool) (A : ℕ → Bool → Bool) (x : List Bool),
          x.length = m * 2 ^ (w + 1) + 2 * n →
          (∀ i < m, ∀ a < 2 ^ (w + 1), x.getD (i * 2 ^ (w + 1) + a) false = T i a) →
          (∀ j < n, ∀ b : Bool, x.getD (m * 2 ^ (w + 1) + 2 * j + (if b then 1 else 0)) false = A j b) →
          ∀ b : Fin (n + 1),
            (C.wires x).getD (outBit b) false = (total n m w d e T A % 2 ^ (n + 1)).testBit b.val

theorem glue (hcomb : CombStatement) (hcirc : CircStatementLe) :
    ∀ (n m w : Nat) (hn : 0 < n) (hm : 0 < m), m ≤ n →
  let tableInputs := m * 2 ^ (w + 1)
  let inputs := tableInputs + 2 * n
  let d := min w (n - 1)
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (outBit : Fin (n + 1) → Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
    C.size ≤ 16 * (n + 1) ^ 2 * 2 ^ (d + (m + d - n)) + 2 ∧
    C.output = outBit 0 ∧ (∀ j, outBit j < inputs + C.size) ∧
    ∀ (table : Fin m → (Fin (w + 1) → Bool) → Bool) (allow : Fin n → Bool → Bool),
      let wiresIn := List.ofFn (fun a : Fin inputs =>
        if a.val < tableInputs then
          table ⟨(a.val / 2 ^ (w + 1)) % m, Nat.mod_lt _ hm⟩
            (fun b => (a.val % 2 ^ (w + 1)).testBit b.val)
        else
          let t := a.val - tableInputs
          allow ⟨(t / 2) % n, Nat.mod_lt _ hn⟩ (decide (t % 2 = 1)))
      let sols := Finset.univ.filter (fun z : Fin (2 ^ n) =>
        (∀ j : Fin n, allow j (z.val.testBit j.val) = true) ∧
        ∀ i : Fin m, table i (fun p => z.val.testBit ((i.val + p.val) % n)) = true)
      ∀ b : Fin (n + 1), (C.wires wiresIn).getD (outBit b) false = sols.card.testBit b.val := by
  intro n m w hn hm hmn
  obtain ⟨C, outBit, h1, h2, h3, h4, h5, h6⟩ :=
    hcirc n m w (min w (n - 1)) (m + min w (n - 1) - n) hn hm hmn
  refine ⟨C, outBit, h1, h2, h3, h4, h5, ?_⟩
  intro table allow wiresIn sols b
  have hpos : 0 < 2 ^ (w + 1) := Nat.pos_of_ne_zero (by positivity)
  have key := h6 (fun i a => table ⟨i % m, Nat.mod_lt _ hm⟩ (fun b => a.testBit b.val))
    (fun j b => allow ⟨j % n, Nat.mod_lt _ hn⟩ b) wiresIn (by simp [wiresIn]) ?_ ?_ b
  · rw [key, ← hcomb n m w hn hm hmn table allow]
    have hcard : sols.card < 2 ^ (n + 1) := by
      calc sols.card ≤ (Finset.univ : Finset (Fin (2 ^ n))).card := Finset.card_filter_le _ _
        _ = 2 ^ n := by simp
        _ < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [Nat.mod_eq_of_lt hcard]
  · intro i hi a ha
    have hlt : i * 2 ^ (w + 1) + a < m * 2 ^ (w + 1) := by
      calc i * 2 ^ (w + 1) + a < i * 2 ^ (w + 1) + 2 ^ (w + 1) := by omega
        _ = (i + 1) * 2 ^ (w + 1) := by ring
        _ ≤ m * 2 ^ (w + 1) := Nat.mul_le_mul_right _ hi
    have hlt2 : i * 2 ^ (w + 1) + a < m * 2 ^ (w + 1) + 2 * n := by omega
    have hdiv : (i * 2 ^ (w + 1) + a) / 2 ^ (w + 1) = i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt ha, Nat.zero_add]
    have hmod : (i * 2 ^ (w + 1) + a) % 2 ^ (w + 1) = a := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
    simp only [wiresIn, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt2, dite_true,
      Option.getD_some, hlt, ite_true, hdiv, hmod]
  · intro j hj b
    have hlt2 : m * 2 ^ (w + 1) + 2 * j + (if b then 1 else 0) < m * 2 ^ (w + 1) + 2 * n := by
      split <;> omega
    have hnl : ¬ (m * 2 ^ (w + 1) + 2 * j + (if b then 1 else 0) < m * 2 ^ (w + 1)) := by omega
    have hsub : m * 2 ^ (w + 1) + 2 * j + (if b then 1 else 0) - m * 2 ^ (w + 1)
        = 2 * j + (if b then 1 else 0) := by omega
    have hd : (2 * j + (if b then 1 else 0)) / 2 = j := by split <;> omega
    have hb : decide ((2 * j + (if b then 1 else 0)) % 2 = 1) = b := by
      cases b <;> simp
    simp only [wiresIn, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt2, dite_true,
      Option.getD_some, hnl, ite_false, hsub, hd, hb]

end PEqualNP.Outside.L_clb_045

theorem PEqualNP.Outside.L_clb_045 : ∀ (n m w : Nat) (hn : 0 < n) (hm : 0 < m), m ≤ n →
  let tableInputs := m * 2 ^ (w + 1)
  let inputs := tableInputs + 2 * n
  let d := min w (n - 1)
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (outBit : Fin (n + 1) → Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
    C.size ≤ 16 * (n + 1) ^ 2 * 2 ^ (d + (m + d - n)) + 2 ∧
    C.output = outBit 0 ∧ (∀ j, outBit j < inputs + C.size) ∧
    ∀ (table : Fin m → (Fin (w + 1) → Bool) → Bool) (allow : Fin n → Bool → Bool),
      let wiresIn := List.ofFn (fun a : Fin inputs =>
        if a.val < tableInputs then
          table ⟨(a.val / 2 ^ (w + 1)) % m, Nat.mod_lt _ hm⟩
            (fun b => (a.val % 2 ^ (w + 1)).testBit b.val)
        else
          let t := a.val - tableInputs
          allow ⟨(t / 2) % n, Nat.mod_lt _ hn⟩ (decide (t % 2 = 1)))
      let sols := Finset.univ.filter (fun z : Fin (2 ^ n) =>
        (∀ j : Fin n, allow j (z.val.testBit j.val) = true) ∧
        ∀ i : Fin m, table i (fun p => z.val.testBit ((i.val + p.val) % n)) = true)
      ∀ b : Fin (n + 1), (C.wires wiresIn).getD (outBit b) false = sols.card.testBit b.val :=
  PEqualNP.Outside.L_clb_045.glue PEqualNP.Outside.L_clb_045.comb PEqualNP.Outside.L_clb_045.circ_le
