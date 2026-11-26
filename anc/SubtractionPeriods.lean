import Std

/-!
Formalization for “Pair-Sum Periods in Three-Move Subtraction Games”.

The endpoints are `miklos_post_conjecture_3_original` and
`manabe_conjecture_57_canonical`. Build with Lean 4.19.0 and Std.
-/

namespace SubtractionPeriods

/-- The normal-play losing-position recurrence. The zero move is ignored. -/
def IsOutcome (moves : List Nat) (f : Nat → Prop) : Prop :=
  ∀ n, f n ↔ ∀ s ∈ moves, 0 < s → s ≤ n → ¬ f (n - s)

/-- The canonical losing predicate of normal-play subtraction. -/
def Losing (moves : List Nat) (n : Nat) : Prop :=
  ∀ s ∈ moves, ∀ _hs : 0 < s ∧ s ≤ n, ¬ Losing moves (n - s)
termination_by n
decreasing_by omega

theorem losing_outcome (moves : List Nat) : IsOutcome moves (Losing moves) := by
  intro n
  rw [Losing]
  exact ⟨fun h s hm hp hl => h s hm ⟨hp, hl⟩,
    fun h s hm hs => h s hm hs.1 hs.2⟩

def Period (f : Nat → Prop) (p : Nat) := ∀ n, f (n+p) ↔ f n

def LeastPeriod (f : Nat → Prop) (p : Nat) :=
  0 < p ∧ Period f p ∧ ∀ d, 0 < d → Period f d → p ≤ d

private theorem no_move {S : List Nat} {f : Nat → Prop} (hf : IsOutcome S f)
    {n s : Nat} (hm : s ∈ S) (hs : 0 < s) (x : f n) : ¬ f (n+s) := by
  intro h
  have h' := (hf (n+s)).mp h s hm hs (by omega)
  exact h' (by simpa using x)

private theorem reply {S : List Nat} {f : Nat → Prop} (hf : IsOutcome S f)
    {n : Nat} (hn : ¬ f n) : ∃ s ∈ S, 0 < s ∧ s ≤ n ∧ f (n-s) := by
  classical
  apply Classical.byContradiction
  intro h
  apply hn
  apply (hf n).mpr
  intro s hm hp hl hs
  exact h ⟨s, hm, hp, hl, hs⟩

private theorem outcome_of_rules {S : List Nat} {f : Nat → Prop}
    (independent : ∀ n s, s ∈ S → 0 < s → f n → ¬ f (n+s))
    (dominating : ∀ n, ¬ f n → ∃ s ∈ S, 0 < s ∧ s ≤ n ∧ f (n-s)) :
    IsOutcome S f := by
  intro n
  constructor
  · intro h s hm hp hl hx
    have hh := independent (n-s) s hm hp hx
    rw [Nat.sub_add_cancel hl] at hh
    exact hh h
  · intro h
    apply Classical.byContradiction
    intro hn
    obtain ⟨s, hm, hp, hl, hx⟩ := dominating n hn
    exact h s hm hp hl hx

private theorem agree_below {S T : List Nat} {f g : Nat → Prop}
    (hf : IsOutcome S f) (hg : IsOutcome T g) {p : Nat}
    (hST : ∀ s, 0 < s → s < p → (s ∈ S ↔ s ∈ T)) :
    ∀ n, n < p → (f n ↔ g n) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    rw [hf n, hg n]
    constructor
    · intro h s hm hs hsn hx
      exact h s ((hST s hs (by omega)).mpr hm) hs hsn
        ((ih (n-s) (by omega) (by omega)).mpr hx)
    · intro h s hm hs hsn hx
      exact h s ((hST s hs (by omega)).mp hm) hs hsn
        ((ih (n-s) (by omega) (by omega)).mp hx)

private theorem unique_outcome {S : List Nat} {f g : Nat → Prop}
    (hf : IsOutcome S f) (hg : IsOutcome S g) (n : Nat) : f n ↔ g n :=
  agree_below hf hg (p := n+1) (fun _ _ _ => Iff.rfl) n (by omega)

private theorem period_add_mul {f : Nat → Prop} {p : Nat} (hp : Period f p)
    (n k : Nat) : f (n + p*k) ↔ f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, hp (n+p*k), ih]

private theorem period_mod {f : Nat → Prop} {p : Nat} (hp : Period f p)
    (n : Nat) : f n ↔ f (n%p) := by
  have h := period_add_mul hp (n%p) (n/p)
  rwa [Nat.mod_add_div] at h

private theorem period_of_mod {f : Nat → Prop} {p : Nat}
    (hp : ∀ n, f n ↔ f (n%p)) : Period f p := by
  intro n
  rw [hp (n+p), hp n, Nat.add_mod_right]

private theorem least_dvd {f : Nat → Prop} {p d : Nat}
    (hp : Period f p) (hd : LeastPeriod f d) : d ∣ p := by
  have hr : Period f (p%d) := by
    intro n
    have h := period_add_mul hd.2.1 (n+p%d) (p/d)
    rw [Nat.add_assoc, Nat.mod_add_div] at h
    exact h.symm.trans (hp n)
  have hz : p%d = 0 := by
    have hh := Nat.mod_lt p hd.1
    apply Classical.byContradiction
    intro h
    have := hd.2.2 (p%d) (by omega) hr
    omega
  exact Nat.dvd_of_mod_eq_zero hz

private theorem least_of_period {f : Nat → Prop} {p : Nat} (hp : 0 < p)
    (hperiod : Period f p) : ∃ d, LeastPeriod f d := by
  classical
  have h : ∀ n, 0 < n → Period f n → ∃ d, LeastPeriod f d := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn hf
      by_cases ht : ∃ d, d < n ∧ 0 < d ∧ Period f d
      · obtain ⟨d, hdn, hd, hdf⟩ := ht
        exact ih d hdn hd hdf
      · refine ⟨n, hn, hf, ?_⟩
        intro d hd he
        apply Classical.byContradiction
        intro hh
        exact ht ⟨d, by omega, hd, he⟩
  exact h p hp hperiod

/-- Complementary move distances characterize repetition of the actual initial block. -/
theorem period_iff_wrap {S : List Nat} {f : Nat → Prop} (hf : IsOutcome S f)
    {p : Nat} (hp : 0 < p) (hS : ∀ s ∈ S, s < p) :
    Period f p ↔ ∀ s ∈ S, 0 < s → ∀ x, x+(p-s) < p → f x → ¬ f (x+(p-s)) := by
  constructor
  · intro h s hm hs x _ hx hy
    have hh := no_move hf hm hs hy
    have he : x+(p-s)+s = x+p := by have := hS s hm; omega
    rw [he] at hh
    exact hh ((h x).mpr hx)
  · intro hwrap
    let g := fun n => f (n%p)
    have hg : IsOutcome S g := by
      apply outcome_of_rules
      · intro n s hm hs hx hy
        let r := n%p
        have hr : r < p := Nat.mod_lt _ hp
        have hsp := hS s hm
        change f r at hx
        change f ((n+s)%p) at hy
        rw [Nat.add_mod n s p, Nat.mod_eq_of_lt hsp] at hy
        change f ((r+s)%p) at hy
        by_cases h : r+s < p
        · rw [Nat.mod_eq_of_lt h] at hy
          exact no_move hf hm hs hx hy
        · have he : (r+s)%p = r+s-p := by
            rw [Nat.mod_eq_sub_mod (by omega : p ≤ r+s),
              Nat.mod_eq_of_lt (by omega : r+s-p < p)]
          rw [he] at hy
          have hback : r+s-p+(p-s) = r := by omega
          exact hwrap s hm hs (r+s-p) (by rwa [hback]) hy (by rwa [hback])
      · intro n hn
        let r := n%p
        have hr : r ≤ n := Nat.mod_le _ _
        change ¬ f r at hn
        obtain ⟨s, hm, hs, hsr, hx⟩ := reply hf hn
        refine ⟨s, hm, hs, by omega, ?_⟩
        change f ((n-s)%p)
        have he : n-s = r-s + p*(n/p) := by
          have := Nat.mod_add_div n p
          change r + p*(n/p) = n at this
          omega
        rw [he, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (by have := Nat.mod_lt n hp; change r<p at this; omega)]
        exact hx
    exact period_of_mod (unique_outcome hf hg)

private theorem flip {a n : Nat} (ha : 0 < a) :
    (n+a)%(2*a) < a ↔ ¬ n%(2*a) < a := by
  have ha' : a < 2*a := by omega
  have hr := Nat.mod_lt n (by omega : 0 < 2*a)
  rw [Nat.add_mod n a, Nat.mod_eq_of_lt ha']
  by_cases h : n%(2*a) < a
  · rw [Nat.mod_eq_of_lt (by omega : n%(2*a)+a < 2*a)]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega : 2*a ≤ n%(2*a)+a),
      Nat.mod_eq_of_lt (by omega : n%(2*a)+a-2*a < 2*a)]
    omega

private theorem one_move {a : Nat} (ha : 0 < a) :
    IsOutcome [a] (fun n => n%(2*a) < a) := by
  intro n
  simp only [List.mem_singleton]
  by_cases hn : a ≤ n
  · have h := flip (n := n-a) ha
    rw [Nat.sub_add_cancel hn] at h
    simpa [ha, hn] using h
  · have h : n%(2*a) < a := by rw [Nat.mod_eq_of_lt (by omega : n<2*a)]; omega
    simp [hn, h]

/-- The explicit two-move losing residues, with cyclic reduction. -/
def Z (a b n : Nat) : Prop :=
  n%(a+b) < b ∧ (n%(a+b))%(2*a) < a

private theorem Z_small {a b n : Nat} (hn : n < a+b) :
    Z a b n ↔ n < b ∧ n%(2*a) < a := by
  unfold Z
  rw [Nat.mod_eq_of_lt hn]

private theorem Z_period (a b : Nat) : Period (Z a b) (a+b) := by
  intro n
  simp [Z, Nat.add_mod_right]

private theorem Z_congr {a b n m : Nat} (h : n%(a+b) = m%(a+b)) :
    Z a b n ↔ Z a b m := by simp only [Z, h]

private theorem Z_initial {a b n : Nat} (hab : a<b) (hn : n<a) :
    Z a b n := by
  apply (Z_small (by omega)).mpr
  rw [Nat.mod_eq_of_lt (by omega : n<2*a)]
  omega

private theorem Z_outcome {a b : Nat} (ha : 0 < a) (hab : a < b) :
    IsOutcome [a,b] (Z a b) := by
  let f := Losing [a,b]
  have hf := losing_outcome [a,b]
  change IsOutcome [a,b] f at hf
  have hbelow : ∀ n, n < b → (f n ↔ n%(2*a) < a) := by
    apply agree_below hf (one_move ha)
    intro s _ hs
    simp only [List.mem_cons, List.not_mem_nil, or_false, List.mem_singleton]
    omega
  have hp : Period f (a+b) := by
    apply (period_iff_wrap hf (by omega) (by simp; omega)).mpr
    intro s hm hs n _ hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hmove | hmove
    · subst s
      have he : a+b-a = b := by omega
      rw [he]
      exact no_move hf (by simp) (by omega) hx
    · subst s
      have he : a+b-b = a := by omega
      rw [he]
      exact no_move hf (by simp) ha hx
  have he : ∀ n, f n ↔ Z a b n := by
    intro n
    rw [period_mod hp n]
    have hn := Nat.mod_lt n (by omega : 0<a+b)
    change f (n%(a+b)) ↔ _
    unfold Z
    by_cases hh : n%(a+b)<b
    · simp [hh, hbelow _ hh]
    · have hn' : n%(a+b)-b < a := by omega
      have hx : f (n%(a+b)-b) := (hbelow _ (by omega)).mpr (by
        rw [Nat.mod_eq_of_lt (by omega : n%(a+b)-b < 2*a)]
        omega)
      have hz := no_move hf (by simp : b ∈ [a,b]) (by omega) hx
      rw [Nat.sub_add_cancel (by omega : b ≤ n%(a+b))] at hz
      simp [hz, hh]
  have heq : f = Z a b := funext fun n => propext (he n)
  exact heq ▸ hf

abbrev Y (a b c : Nat) := Losing [a,b,c]

private theorem below_c {a b c n : Nat} (ha : 0 < a) (hab : a<b) (hn : n<c) :
    Y a b c n ↔ Z a b n := by
  apply agree_below (losing_outcome [a,b,c]) (Z_outcome ha hab) (p := c) _ n hn
  intro s _ hs
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

private theorem initial_Y {a b c n : Nat} (ha : 0<a) (hab : a<b) (hbc : b<c)
    (hn : n<a) : Y a b c n :=
  (below_c ha hab (by omega)).mpr (Z_initial hab hn)

private theorem tail {a b c u : Nat} (ha : 0<a) (hab : a<b) (hbc : b<c) (hu : u<b) :
    Y a b c (c+u) ↔ ¬ Z a b u ∧ ¬ Z a b (c+u-b) := by
  have hf := losing_outcome [a,b,c]
  change IsOutcome [a,b,c] (Y a b c) at hf
  have hU := below_c (n := u) ha hab (by omega : u<c)
  have hB := below_c (n := c+u-b) ha hab (by omega : c+u-b<c)
  have hC : c+u-c = u := by omega
  constructor
  · intro h
    have hh := (hf _).mp h
    refine ⟨fun hz => ?_, fun hz => ?_⟩
    · exact hh c (by simp) (by omega) (by omega) (by simpa only [hC] using hU.mpr hz)
    · exact hh b (by simp) (by omega) (by omega) (hB.mpr hz)
  · rintro ⟨hnu, hnb⟩
    have hua : a ≤ u := by
      apply Classical.byContradiction
      intro hh
      exact hnu (Z_initial hab (by omega))
    have hza : Z a b (u-a) := by
      have hflip := flip (n := u-a) ha
      rw [Nat.sub_add_cancel hua] at hflip
      have h0 : ¬ u%(2*a)<a := fun h => hnu ((Z_small (by omega)).mpr ⟨hu,h⟩)
      apply (Z_small (by omega)).mpr
      refine ⟨by omega, ?_⟩
      apply Classical.byContradiction
      intro h
      exact h0 (hflip.mpr h)
    apply (hf _).mpr
    intro s hm hs hsle hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hmove | hmove | hmove
    · subst s
      have hh := no_move hf (by simp : c ∈ [a,b,c]) (by omega) ( (below_c ha hab (by omega : u-a<c)).mpr hza)
      have he : u-a+c = c+u-a := by omega
      exact hh (he.symm ▸ hx)
    · subst s
      exact hnb (hB.mp hx)
    · subst s
      exact hnu (hU.mp (by simpa only [hC] using hx))


/-- The part of the interval below b that is winning and lies at or above a. -/
def D (a b u : Nat) : Prop := a ≤ u ∧ u < b ∧ ¬ Z a b u

/-- The winning part of the last a positions below b. -/
def Lambda (a b u : Nat) : Prop := b-a ≤ u ∧ u < b ∧ ¬ Z a b u

def LongTest (a b c : Nat) : Prop :=
  ∀ u, Lambda a b u → Z a b (c+u+a)

/-- The c+a rotation-avoidance test, written with a nonnegative representative. -/
def MiddleTest (a b c : Nat) : Prop :=
  ∀ x, x < b-a → Z a b x → ¬ Z a b (c+x-(b-a))

/-- Adding c leaves a losing-to-losing edge in the two-move pattern. -/
def Collision (a b c : Nat) : Prop := ∃ x, Z a b x ∧ Z a b (x+c)

private theorem middle_prefix {a b c n : Nat} (ha : 0<a) (hab : a<b) (hbc : b<c)
    (hn : n<c+a) : Y a b c n ↔ n<c ∧ Z a b n := by
  by_cases hh : n<c
  · simp [hh, below_c ha hab hh]
  · have hnot : ¬ Y a b c n := by
      have h := tail (c:=c) (u:=n-c) ha hab hbc (by omega)
      rw [show c+(n-c)=n by omega] at h
      exact fun hy => (h.mp hy).1 (Z_initial hab (by omega))
    simp [hh, hnot]

/-- If a positive period is at most max(c,a+b), the third move is inert. -/
theorem short_period_inert {a b c p : Nat} (ha : 0<a) (hab : a<b) (hbc : b<c)
    (hp : 0<p) (hle : p≤max c (a+b)) (hperiod : Period (Y a b c) p) :
    ∀ n, Y a b c n ↔ Z a b n := by
  have hf := losing_outcome [a,b,c]
  change IsOutcome [a,b,c] (Y a b c) at hf
  have hz := Z_outcome ha hab
  have hprefix : ∀ n, n<p → (Y a b c n ↔ Z a b n) := by
    intro n hn
    by_cases hnc : n<c
    · exact below_c ha hab hnc
    · have hnM : n<a+b := by omega
      have hY := middle_prefix (n := n) ha hab hbc (by omega)
      have hZ := Z_small (a := a) (b := b) hnM
      have hnb : ¬ n<b := by omega
      simp_all
  apply unique_outcome _ hz
  apply outcome_of_rules
  · intro n s hm hs hx
    have hm' : s ∈ [a,b,c] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
      omega
    exact no_move hf hm' hs hx
  · intro n hn
    let r := n%p
    have hr : r<p := Nat.mod_lt n hp
    have hrn : r≤n := Nat.mod_le n p
    have hn' : ¬ Z a b r := fun h =>
      hn ((period_mod hperiod n).mpr ((hprefix r hr).mpr h))
    obtain ⟨s, hm, hs, hsr, hx⟩ := reply hz hn'
    refine ⟨s, hm, hs, by omega, ?_⟩
    have he : n-s = r-s+p*(n/p) := by
      have := Nat.mod_add_div n p
      change r+p*(n/p)=n at this
      omega
    rw [he]
    exact (period_add_mul hperiod (r-s) (n/p)).mpr
      ((hprefix (r-s) (by omega)).mpr hx)

private theorem inert_iff {a b c : Nat} (ha : 0<a) (hab : a<b) (hbc : b<c) :
    (∀ n, Y a b c n ↔ Z a b n) ↔ ¬ Collision a b c := by
  have hf := losing_outcome [a,b,c]
  change IsOutcome [a,b,c] (Y a b c) at hf
  have hz := Z_outcome ha hab
  constructor
  · intro he h
    obtain ⟨x,hx,hy⟩ := h
    exact no_move hf (by simp : c ∈ [a,b,c]) (by omega) ((he x).mpr hx) ((he _).mpr hy)
  · intro h
    apply unique_outcome hf
    apply outcome_of_rules
    · intro n s hm hs hx hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with hmove | hmove | hmove
      · subst s
        exact no_move hz (by simp) ha hx hy
      · subst s
        exact no_move hz (by simp) (by omega) hx hy
      · subst s
        exact h ⟨n,hx,hy⟩
    · intro n hn
      obtain ⟨s,hm,hs,hle,hx⟩ := reply hz hn
      have hm' : s ∈ [a,b,c] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
        omega
      exact ⟨s,hm',hs,hle,hx⟩

theorem period_short_iff {a b c : Nat} (ha : 0<a) (hab : a<b) (hbc : b<c) :
    Period (Y a b c) (a+b) ↔ ¬ Collision a b c := by
  have hi := inert_iff ha hab hbc
  constructor
  · intro h
    exact hi.mp (short_period_inert ha hab hbc (by omega) (by omega) h)
  · intro h n
    rw [hi.mpr h (n+(a+b)), hi.mpr h n, Z_period]

theorem period_middle_iff {a b c : Nat} (ha : 0<a) (hab : a<b) (hbc : b<c) :
    Period (Y a b c) (c+a) ↔ MiddleTest a b c := by
  have hf := losing_outcome [a,b,c]
  change IsOutcome [a,b,c] (Y a b c) at hf
  rw [period_iff_wrap hf (by omega) (by simp; omega)]
  constructor
  · intro hw x hxd hx hy
    have he : x+(c+a-b) = c+x-(b-a) := by omega
    have hxt : x<c+a := by omega
    have hyt : x+(c+a-b)<c+a := by omega
    exact hw b (by simp) (by omega) x hyt
      ((middle_prefix ha hab hbc hxt).mpr ⟨by omega,hx⟩)
      ((middle_prefix ha hab hbc hyt).mpr ⟨by omega, he.symm ▸ hy⟩)
  · intro ht s hm hs x hx hY hV
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hmove | hmove | hmove
    · subst s
      have he : c+a-a=c := by omega
      rw [he] at hV
      exact no_move hf (by simp : c ∈ [a,b,c]) (by omega) hY hV
    · subst s
      have hX := (middle_prefix ha hab hbc (by omega : x<c+a)).mp hY
      have hV' := (middle_prefix ha hab hbc hx).mp hV
      have he : x+(c+a-b) = c+x-(b-a) := by omega
      exact ht x (by omega) hX.2 (he ▸ hV'.2)
    · subst s
      have he : c+a-c=a := by omega
      rw [he] at hV
      exact no_move hf (by simp : a ∈ [a,b,c]) ha hY hV

theorem period_long_iff {a b c : Nat} (ha : 0<a) (hab : a<b) (hbc : b<c) :
    Period (Y a b c) (c+b) ↔ LongTest a b c := by
  classical
  have hf := losing_outcome [a,b,c]
  change IsOutcome [a,b,c] (Y a b c) at hf
  have htranslate : ∀ u, Z a b (c+u-b) ↔ Z a b (c+u+a) := by
    intro u
    have he : c+u-b+(a+b)=c+u+a := by omega
    rw [← he, Z_period]
  rw [period_iff_wrap hf (by omega) (by simp; omega)]
  constructor
  · intro hw u hu
    obtain ⟨hl,hr,hn⟩ := hu
    let x := u-(b-a)
    have hxa : x<a := by dsimp [x]; omega
    have he : x+(c+b-a)=c+u := by dsimp [x]; omega
    have hnY := hw a (by simp) ha x (by rw [he]; omega)
      (initial_Y ha hab hbc hxa)
    rw [he, tail ha hab hbc hr] at hnY
    exact (htranslate u).mp (Classical.byContradiction fun hh => hnY ⟨hn,hh⟩)
  · intro ht s hm hs x hx hY hV
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hmove | hmove | hmove
    · subst s
      let u := x+(b-a)
      have hu : u<b := by dsimp [u]; omega
      have he : x+(c+b-a)=c+u := by dsimp [u]; omega
      rw [he, tail ha hab hbc hu] at hV
      exact hV.2 ((htranslate u).mpr (ht u ⟨by dsimp [u]; omega,hu,hV.1⟩))
    · subst s
      have he : c+b-b=c := by omega
      rw [he] at hV
      exact no_move hf (by simp : c ∈ [a,b,c]) (by omega) hY hV
    · subst s
      have he : c+b-c=b := by omega
      rw [he] at hV
      exact no_move hf (by simp : b ∈ [a,b,c]) (by omega) hY hV

theorem least_long_iff {a b c : Nat} (ha : 0<a) (hab : a<b) (hbc : b<c) :
    LeastPeriod (Y a b c) (c+b) ↔ LongTest a b c ∧ Collision a b c := by
  classical
  have hlong := period_long_iff ha hab hbc
  have hshort := period_short_iff ha hab hbc
  constructor
  · intro h
    refine ⟨hlong.mp h.2.1, ?_⟩
    apply Classical.byContradiction
    intro hc
    have := h.2.2 (a+b) (by omega) (hshort.mpr hc)
    omega
  · rintro ⟨ht,hc⟩
    have hp := hlong.mpr ht
    obtain ⟨d,hd⟩ := least_of_period (by omega : 0<c+b) hp
    have hle := hd.2.2 (c+b) (by omega) hp
    have heq : d=c+b := by
      apply Classical.byContradiction
      intro hn
      obtain ⟨k,hk⟩ := least_dvd hp hd
      have hk2 : 2≤k := by
        apply Classical.byContradiction
        intro hh
        have hk01 : k=0 ∨ k=1 := by omega
        rcases hk01 with rfl | rfl <;> simp_all
      have hmul := Nat.mul_le_mul_left d hk2
      rw [← hk] at hmul
      have hdc : d≤max c (a+b) := by omega
      exact (inert_iff ha hab hbc).mp (short_period_inert ha hab hbc hd.1 hdc hd.2.1) hc
    exact heq ▸ hd


private theorem phase_block {a k t : Nat} (ht : t<2*a) :
    (2*a*k+t)%(2*a) = t := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]

private theorem Lambda_odd {a b h r u : Nat} (hb : b=2*a*h+a+r) (hr : r<a) :
    Lambda a b u ↔ 2*a*h+a ≤ u ∧ u<b := by
  unfold Lambda
  by_cases hu : b-a ≤ u ∧ u<b
  · have he : 2*a*h+(u-2*a*h)=u := by omega
    have hm := phase_block (a:=a) (k:=h) (t:=u-2*a*h) (by omega)
    rw [he] at hm
    have hz := Z_small (a:=a) (b:=b) (n:=u) (by omega)
    rw [hm] at hz
    constructor
    · intro hx
      refine ⟨?_,hu.2⟩
      have : ¬ u-2*a*h<a := fun hp => hx.2.2 (hz.mpr ⟨hu.2,hp⟩)
      omega
    · intro h
      exact ⟨hu.1,hu.2,fun hz' => by have := (hz.mp hz').2; omega⟩
  · constructor
    · intro h
      exact False.elim (hu ⟨h.1,h.2.1⟩)
    · intro h
      exact False.elim (hu ⟨by omega,h.2⟩)

private theorem Lambda_even {a b h r u : Nat} (hb : b=2*a*(h+1)+r) (hr : r<a) :
    Lambda a b u ↔ 2*a*h+a+r ≤ u ∧ u<2*a*(h+1) := by
  rw [Nat.mul_succ] at hb
  unfold Lambda
  by_cases hu : b-a ≤ u ∧ u<b
  · have hz := Z_small (a:=a) (b:=b) (n:=u) (by omega)
    by_cases hh : u<2*a*h+2*a
    · have he : 2*a*h+(u-2*a*h)=u := by omega
      have hm := phase_block (a:=a) (k:=h) (t:=u-2*a*h) (by omega)
      rw [he] at hm
      rw [hm] at hz
      rw [Nat.mul_succ]
      exact ⟨fun _ => ⟨by omega,hh⟩,
        fun _ => ⟨hu.1,hu.2,fun hz' => by have := (hz.mp hz').2; omega⟩⟩
    · have hm := phase_block (a:=a) (k:=h+1) (t:=u-2*a*(h+1))
          (by rw [Nat.mul_succ]; omega)
      rw [show 2*a*(h+1)+(u-2*a*(h+1))=u by rw [Nat.mul_succ]; omega] at hm
      rw [hm, Nat.mul_succ] at hz
      rw [Nat.mul_succ]
      exact ⟨fun h => False.elim (h.2.2 (hz.mpr ⟨hu.2,by omega⟩)),
        fun h => False.elim (hh h.2)⟩
  · rw [Nat.mul_succ]
    exact ⟨fun h => False.elim (hu ⟨h.1,h.2.1⟩),
      fun h => False.elim (hu ⟨by omega,by omega⟩)⟩

private def Fits (a b s len : Nat) : Prop :=
  ∀ i, i<len → Z a b (s+i)

private theorem fits_congr {a b s s' len : Nat} (he : s%(a+b)=s'%(a+b)) :
    Fits a b s len ↔ Fits a b s' len := by
  have hh (i : Nat) : Z a b (s+i) ↔ Z a b (s'+i) := by
    apply Z_congr
    rw [Nat.add_mod s i, Nat.add_mod s' i, he]
  exact ⟨fun h i hi => (hh i).mp (h i hi), fun h i hi => (hh i).mpr (h i hi)⟩

private theorem fits_iff {a b s len : Nat} (ha : 0<a) (hs : s<a+b) (hlen : 0<len) :
    Fits a b s len ↔ s+len ≤ b ∧ s%(2*a)+len ≤ a := by
  have hphase (i : Nat) (hi : s%(2*a)+i<2*a) :
      (s+i)%(2*a) = s%(2*a)+i := by
    rw [Nat.add_mod s i, Nat.mod_eq_of_lt (by omega : i<2*a), Nat.mod_eq_of_lt hi]
  constructor
  · intro h
    have h0 : Z a b s := by simpa using h 0 hlen
    obtain ⟨hsb,hst⟩ := (Z_small hs).mp h0
    have hB : s+len ≤ b := by
      by_cases he : s+len ≤ b
      · exact he
      · have hh := h (b-s) (by omega)
        rw [show s+(b-s)=b by omega] at hh
        have := ((Z_small (by omega : b<a+b)).mp hh).1
        omega
    refine ⟨hB,?_⟩
    by_cases he : s%(2*a)+len ≤ a
    · exact he
    · let i := a-s%(2*a)
      have hi : i<len := by dsimp [i]; omega
      have hh := (Z_small (by omega : s+i<a+b)).mp (h i hi)
      rw [hphase i (by dsimp [i]; omega)] at hh
      dsimp [i] at hh
      omega
  · rintro ⟨hB,hT⟩ i hi
    apply (Z_small (by omega : s+i<a+b)).mpr
    rw [hphase i (by omega)]
    omega

private theorem long_to_fit_even {a b c h r : Nat}
    (hbc : b<c) (hb : b=2*a*(h+1)+r) (hr : r<a) :
    LongTest a b c ↔ Fits a b ((c-a)%(a+b)) (a-r) := by
  let l := 2*a*h+a+r
  have hla : l+a=b := by dsimp [l]; rw [Nat.mul_succ] at hb; omega
  have hla' : c+l+a=(c-a)+(a+b) := by
    have : a ≤ b := by dsimp [l] at hla; omega
    omega
  have hI : ∀ u, Lambda a b u ↔ l≤u ∧ u<l+(a-r) := by
    intro u
    rw [Lambda_even hb hr]
    dsimp [l]
    rw [Nat.mul_succ]
    omega
  have hE : LongTest a b c ↔ Fits a b (c+l+a) (a-r) := by
    constructor
    · intro ht i hi
      have hh := ht (l+i) ((hI _).mpr ⟨by omega,by omega⟩)
      exact (show c+(l+i)+a=c+l+a+i by omega) ▸ hh
    · intro ht u hu
      have hh := (hI _).mp hu
      have he : c+l+a+(u-l)=c+u+a := by omega
      exact he ▸ ht (u-l) (by omega)
  rw [hE]
  apply fits_congr
  rw [hla', Nat.add_mod_right, Nat.mod_mod]

private theorem long_to_fit_odd {a b c h r : Nat}
    (hb : b=2*a*h+a+r) (hr : r<a) :
    LongTest a b c ↔ Fits a b (c+2*a*h+2*a) r := by
  let l := 2*a*h+a
  have hI : ∀ u, Lambda a b u ↔ l≤u ∧ u<l+r := by
    intro u
    rw [Lambda_odd hb hr]
    dsimp [l]
    omega
  constructor
  · intro ht i hi
    have hh := ht (l+i) ((hI _).mpr ⟨by omega,by omega⟩)
    exact (show c+(l+i)+a=c+2*a*h+2*a+i by dsimp [l]; omega) ▸ hh
  · intro ht u hu
    have hh := (hI _).mp hu
    have he : c+2*a*h+2*a+(u-l)=c+u+a := by dsimp [l] at *; omega
    exact he ▸ ht (u-l) (by omega)

private theorem mul_mono (a : Nat) {x y : Nat} (h : x≤y) : 2*a*x ≤ 2*a*y :=
  Nat.mul_le_mul_left _ h

private theorem even_fit_arithmetic {a b s h r : Nat} (ha : 0<a) (hr : r<a)
    (hb : b=2*a*h+r) (hs : s<a+b) :
    Fits a b s (a-r) ↔
      s%(2*a)≤r ∧ s/(2*a)≤h ∧ (s/(2*a)=h → s%(2*a)+a≤2*r) := by
  rw [fits_iff ha hs (by omega)]
  let k := s/(2*a)
  let t := s%(2*a)
  have he : t+2*a*k=s := Nat.mod_add_div s (2*a)
  change (s+(a-r)≤b ∧ t+(a-r)≤a) ↔ (t≤r ∧ k≤h ∧ (k=h → t+a≤2*r))
  constructor
  · rintro ⟨hsb,htr⟩
    have hkh : k≤h := by
      by_cases hh : k≤h
      · exact hh
      · have hm := mul_mono a (show h+1≤k by omega)
        rw [Nat.mul_succ] at hm
        omega
    refine ⟨by omega,hkh,?_⟩
    intro hEq
    rw [hEq] at he
    omega
  · rintro ⟨ht,hkh,heq⟩
    refine ⟨?_,by omega⟩
    by_cases hh : k=h
    · have h := heq hh
      rw [hh] at he
      omega
    · have hm := mul_mono a (show k+1≤h by omega)
      rw [Nat.mul_succ] at hm
      omega

private theorem odd_fit_arithmetic {a b c h r : Nat} (ha : 0<a) (hr : r<a) (hr0 : 0<r)
    (hb : b=2*a*h+a+r) :
    LongTest a b c ↔ r≤(c%(a+b))%(2*a) ∧ (c%(a+b))%(2*a)≤a := by
  let rho := c%(a+b)
  have hR : rho<a+b := Nat.mod_lt _ (by omega)
  let s := (c+2*a*h+2*a)%(a+b)
  have hs : s<a+b := Nat.mod_lt _ (by omega)
  have hS : s=(rho+(a+b)-r)%(a+b) := by
    have he : 2*a*h+2*a = a+b-r := by omega
    dsimp [s,rho]
    rw [show c+2*a*h+2*a=c+(a+b-r) by omega, Nat.add_mod c,
      Nat.mod_eq_of_lt (by omega : a+b-r<a+b)]
    congr 1
    omega
  have hF := fits_congr (a:=a) (b:=b) (len:=r)
      (show (c+2*a*h+2*a)%(a+b)=s%(a+b) by rw [Nat.mod_eq_of_lt hs])
  rw [long_to_fit_odd hb hr, hF, fits_iff ha hs hr0]
  have hlt : rho<r → s>b := by
    intro hh
    rw [hS, Nat.mod_eq_of_lt (by omega : rho+(a+b)-r<a+b)]
    omega
  have hsub : r≤rho → s=rho-r := by
    intro hh
    rw [hS, show rho+(a+b)-r=(rho-r)+(a+b) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : rho-r<a+b)]
  let k := rho/(2*a)
  let t := rho%(2*a)
  have he : t+2*a*k=rho := Nat.mod_add_div rho (2*a)
  have htmax : t<2*a := Nat.mod_lt _ (by omega)
  change (s+r≤b ∧ s%(2*a)+r≤a) ↔ (r≤t ∧ t≤a)
  constructor
  · rintro ⟨hsb,hsp⟩
    have hrr : r≤rho := by
      by_cases hh : rho<r
      · have := hlt hh
        omega
      · omega
    rw [hsub hrr] at hsp
    by_cases hrt : r≤t
    · have he' : rho-r=2*a*k+(t-r) := by omega
      rw [he', phase_block (by omega : t-r<2*a)] at hsp
      omega
    · have hk : 0<k := by
        by_cases h0 : k=0
        · simp only [h0, Nat.mul_zero, Nat.add_zero] at he
          exact False.elim (hrt (he.symm ▸ hrr))
        · exact Nat.pos_of_ne_zero h0
      have hmul : 2*a*(k-1)+2*a=2*a*k := by
        have hsucc := Nat.mul_succ (2*a) (k-1)
        rw [show (k-1).succ=k by omega] at hsucc
        exact hsucc.symm
      have he' : rho-r=2*a*(k-1)+(2*a+t-r) := by omega
      rw [he', phase_block (by omega : 2*a+t-r<2*a)] at hsp
      omega
  · rintro ⟨hrt,hta⟩
    have hrho : r≤rho := by omega
    have hk : k≤h := by
      by_cases hh : k≤h
      · exact hh
      · have hm := mul_mono a (show h+1≤k by omega)
        rw [Nat.mul_succ] at hm
        omega
    have hm := mul_mono a hk
    rw [hsub hrho, show rho-r=2*a*k+(t-r) by omega,
      phase_block (by omega : t-r<2*a)]
    omega


private theorem collision_residue {a b c : Nat} :
    Collision a b c ↔ ∃ x, Z a b x ∧ Z a b (x+(c%(a+b))) := by
  have h (x : Nat) : Z a b (x+c) ↔ Z a b (x+(c%(a+b))) := by
    apply Z_congr
    rw [Nat.add_mod x c, Nat.add_mod x (c%(a+b)), Nat.mod_mod]
  exact ⟨fun ⟨x,hx,hy⟩ => ⟨x,hx,(h x).mp hy⟩, fun ⟨x,hx,hy⟩ => ⟨x,hx,(h x).mpr hy⟩⟩

private theorem no_collision_at_a {a b c : Nat} (ha : 0<a) (hab : a<b)
    (hrho : c%(a+b)=a) : ¬ Collision a b c := by
  rw [collision_residue, hrho]
  rintro ⟨x,hx,hy⟩
  exact no_move (Z_outcome ha hab) (by simp) ha hx hy

private theorem even_collision {a b c h r : Nat}
    (ha : 0<a) (hab : a<b) (hbc : b<c) (hr : r<a)
    (hb : b=2*a*h+r) (hfit : Fits a b ((c-a)%(a+b)) (a-r)) :
    Collision a b c ↔ 0<(c-a)%(a+b) := by
  let s := (c-a)%(a+b)
  let k := s/(2*a)
  let t := s%(2*a)
  have hs : s<a+b := Nat.mod_lt _ (by omega)
  have he : t+2*a*k=s := Nat.mod_add_div s (2*a)
  have h1 : s+(a-r)≤b := ((fits_iff ha hs (by omega)).mp hfit).1
  have h2 := (even_fit_arithmetic ha hr hb hs).mp hfit
  change t≤r ∧ k≤h ∧ (k=h → t+a≤2*r) at h2
  have hR : c%(a+b)=s+a := by
    rw [← Nat.sub_add_cancel (by omega : a≤c), Nat.add_mod (c-a) a,
      Nat.mod_eq_of_lt (by omega : a<a+b)]
    change (s+a)%(a+b)=s+a
    exact Nat.mod_eq_of_lt (by omega)
  constructor
  · intro hc
    by_cases hh : 0<s
    · exact hh
    · have h0 : s=0 := by omega
      rw [h0, Nat.zero_add] at hR
      exact False.elim (no_collision_at_a ha hab hR hc)
  · intro hh
    rw [collision_residue, hR]
    let x := 2*a*(h-k)+(r-t)
    have hmul : 2*a*(h-k)=2*a*h-2*a*k := Nat.mul_sub_left_distrib _ _ _
    have hm := mul_mono a h2.2.1
    have hx : x+(s+a)=a+b := by dsimp [x]; omega
    refine ⟨x,?_,?_⟩
    · have hxb : x<b := by
        dsimp [x]
        by_cases hk : k=0
        · have ht0 : 0<t := by simp only [hk, Nat.mul_zero, Nat.add_zero] at he; omega
          rw [hk, Nat.sub_zero]
          omega
        · have hkm := mul_mono a (Nat.pos_of_ne_zero hk)
          simp only [Nat.mul_one] at hkm
          omega
      apply (Z_small (by omega : x<a+b)).mpr
      refine ⟨hxb,?_⟩
      dsimp [x]
      rw [phase_block (by omega : r-t<2*a)]
      omega
    · rw [hx]
      simpa only [Nat.zero_add] using (Z_period a b 0).mpr (Z_initial hab ha)

private theorem odd_collision {a b c h r : Nat} (ha : 0<a) (hab : a<b)
    (hr : r<a) (hr0 : 0<r) (hb : b=2*a*h+a+r)
    (hcond : r≤(c%(a+b))%(2*a) ∧ (c%(a+b))%(2*a)≤a) :
    Collision a b c ↔ ((c%(a+b))/(2*a)=0 → (c%(a+b))%(2*a)<a) := by
  let rho := c%(a+b)
  let k := rho/(2*a)
  let t := rho%(2*a)
  have hrho : rho<a+b := Nat.mod_lt _ (by omega)
  have he : t+2*a*k=rho := Nat.mod_add_div rho (2*a)
  change r≤t ∧ t≤a at hcond
  have hk : k≤h := by
    by_cases hh : k≤h
    · exact hh
    · have hmul := mul_mono a (show h+1≤k by omega)
      rw [Nat.mul_succ] at hmul
      omega
  have hmul := mul_mono a hk
  change Collision a b c ↔ (k=0 → t<a)
  constructor
  · intro hc h0
    by_cases hT : t<a
    · exact hT
    · simp only [h0, Nat.mul_zero, Nat.add_zero] at he
      have hh : c%(a+b)=a := by change rho=a; omega
      exact False.elim (no_collision_at_a ha hab hh hc)
  · intro hC
    rw [collision_residue]
    change ∃ x, Z a b x ∧ Z a b (x+rho)
    by_cases hta : t<a
    · refine ⟨0,Z_initial hab ha,?_⟩
      rw [Nat.zero_add]
      exact (Z_small hrho).mpr ⟨by omega,hta⟩
    · have hta' : t=a := by omega
      have hkp : 0<k := by
        by_cases hh : k=0
        · have := hC hh
          omega
        · exact Nat.pos_of_ne_zero hh
      let x := 2*a*h
      let y := 2*a*(k-1)+(a-r)
      have hs := Nat.mul_succ (2*a) (k-1)
      rw [show (k-1).succ=k by omega] at hs
      have hxy : x+rho=y+(a+b) := by dsimp [x,y]; omega
      refine ⟨x,?_,?_⟩
      · apply (Z_small (by dsimp [x]; omega)).mpr
        refine ⟨by dsimp [x]; omega, ?_⟩
        dsimp [x]
        have hzero := phase_block (a:=a) (k:=h) (t:=0) (by omega)
        have heq : (2*a*h)%(2*a)=0 := by simpa only [Nat.add_zero] using hzero
        rwa [heq]
      · rw [hxy, Z_period]
        have hyb : y<b := by dsimp [y]; omega
        apply (Z_small (by omega : y<a+b)).mpr
        refine ⟨hyb,?_⟩
        dsimp [y]
        rw [phase_block (by omega : a-r<2*a)]
        omega

private theorem harmonic_phase {a b h n : Nat} (ha : 0<a) (hb : b=2*a*h+a) :
    Z a b n ↔ n%(2*a)<a := by
  let r := n%(a+b)
  have hr : r<a+b := Nat.mod_lt _ (by omega)
  have hM : a+b=(h+1)*(2*a) := by rw [Nat.mul_comm, Nat.mul_succ]; omega
  have he : r%(2*a)=n%(2*a) := by
    change n%(a+b)%(2*a)=n%(2*a)
    rw [hM, Nat.mod_mul_left_mod]
  unfold Z
  change (r<b ∧ r%(2*a)<a) ↔ n%(2*a)<a
  rw [← he]
  constructor
  · exact And.right
  · intro ht
    refine ⟨?_,ht⟩
    by_cases hrb : r<b
    · exact hrb
    · have hh : r=2*a*h+(r-2*a*h) := by omega
      have hphase := phase_block (a:=a) (k:=h) (t:=r-2*a*h) (by omega)
      have eh : 2*a*h+(r-2*a*h)=r := hh.symm
      rw [eh] at hphase
      omega

private theorem harmonic_collision {a b c h : Nat} (ha : 0<a) (hab : a<b)
    (hb : b=2*a*h+a) :
    Collision a b c ↔ (c%(a+b))%(2*a)≠a := by
  let rho := c%(a+b)
  let t := rho%(2*a)
  have ht : t<2*a := Nat.mod_lt _ (by omega)
  rw [collision_residue]
  change (∃ x, Z a b x ∧ Z a b (x+rho)) ↔ t≠a
  constructor
  · rintro ⟨x,hx,hy⟩ hh
    have hu := (harmonic_phase ha hb).mp hx
    have hv := (harmonic_phase ha hb).mp hy
    rw [Nat.add_mod x rho, show rho%(2*a)=t from rfl, hh,
      Nat.mod_eq_of_lt (by omega : x%(2*a)+a<2*a)] at hv
    omega
  · intro hh
    by_cases he : t<a
    · refine ⟨0,Z_initial hab ha,?_⟩
      rw [Nat.zero_add, harmonic_phase ha hb]
      exact he
    · let x := 2*a-t
      have hxa : x<a := by dsimp [x]; omega
      refine ⟨x,Z_initial hab hxa,?_⟩
      rw [harmonic_phase ha hb, Nat.add_mod x rho,
        Nat.mod_eq_of_lt (by omega : x<2*a), show rho%(2*a)=t from rfl,
        show x+t=2*a by dsimp [x]; omega, Nat.mod_self]
      exact ha

/-- Arithmetic conditions in Miklós–Post, Conjecture 3, with integer
    subtraction in its last even-quotient inequality expressed by addition. -/
def MiklosPostTest (a b c : Nat) : Prop :=
  let q := b/a
  let r := b%a
  let rho := c%(a+b)
  let sigma := (c-a)%(a+b)
  let j := rho/(2*a)
  let t := rho%(2*a)
  let j' := sigma/(2*a)
  let t' := sigma%(2*a)
  if q%2=0 then
    0<sigma ∧ t'≤r ∧ 2*j'≤q ∧ (2*j'=q → t'+a≤2*r)
  else if r=0 then
    t≠a
  else
    r≤t ∧ t≤a ∧ (j=0 → t<a)

/-- The exact statement of Miklós–Post Conjecture 3, with a slightly wider domain. -/
theorem miklos_post_conjecture_3 {a b c : Nat} (ha : 0<a) (hab : a<b) (hbc : b<c) :
    LeastPeriod (Y a b c) (b+c) ↔ MiklosPostTest a b c := by
  rw [Nat.add_comm b c, least_long_iff ha hab hbc]
  let q := b/a
  let r := b%a
  let h := q/2
  have hr : r<a := Nat.mod_lt _ ha
  have hb : r+a*q=b := Nat.mod_add_div b a
  have hq : q%2+2*h=q := Nat.mod_add_div q 2
  unfold MiklosPostTest
  dsimp only
  by_cases hEven : q%2=0
  · rw [if_pos hEven]
    have hq' : q=2*h := by omega
    have hb' : b=2*a*h+r := by
      rw [hq', ← Nat.mul_assoc, Nat.mul_comm a 2] at hb
      omega
    have hh : 0<h := by
      by_cases h0 : h=0
      · rw [h0, Nat.mul_zero, Nat.zero_add] at hb'
        omega
      · exact Nat.pos_of_ne_zero h0
    have hb'' : b=2*a*((h-1)+1)+r := by rwa [show h-1+1=h by omega]
    have hfit := long_to_fit_even (c:=c) hbc hb'' hr
    let s := (c-a)%(a+b)
    have hs : s<a+b := Nat.mod_lt _ (by omega)
    have hA := even_fit_arithmetic ha hr hb' hs
    change (LongTest a b c ∧ Collision a b c) ↔
      0<s ∧ s%(2*a)≤r ∧ 2*(s/(2*a))≤q ∧
      (2*(s/(2*a))=q → s%(2*a)+a≤2*r)
    rw [hfit]
    constructor
    · rintro ⟨hf,hc⟩
      have hh' := hA.mp hf
      refine ⟨(even_collision ha hab hbc hr hb' hf).mp hc, hh'.1, by omega, ?_⟩
      exact fun he => hh'.2.2 (by omega)
    · rintro ⟨hs0,ht,hq2,hh'⟩
      have hf := hA.mpr ⟨ht,by omega,fun he => hh' (by omega)⟩
      exact ⟨hf,(even_collision ha hab hbc hr hb' hf).mpr hs0⟩
  · rw [if_neg hEven]
    have hq' : q=2*h+1 := by omega
    have hb' : b=2*a*h+a+r := by
      rw [hq', Nat.mul_succ, ← Nat.mul_assoc, Nat.mul_comm a 2] at hb
      omega
    by_cases hR0 : r=0
    · rw [if_pos hR0]
      have hh : LongTest a b c := by
        rw [long_to_fit_odd hb' hr, hR0]
        exact fun i hi => False.elim (Nat.not_lt_zero i hi)
      have hb0 : b=2*a*h+a := by omega
      rw [and_iff_right hh, harmonic_collision ha hab hb0]
    · rw [if_neg hR0]
      have hr0 := Nat.pos_of_ne_zero hR0
      rw [odd_fit_arithmetic ha hr hr0 hb']
      constructor
      · rintro ⟨hA,hC⟩
        exact ⟨hA.1,hA.2,(odd_collision ha hab hr hr0 hb' hA).mp hC⟩
      · rintro ⟨h1,h2,h3⟩
        exact ⟨⟨h1,h2⟩,(odd_collision ha hab hr hr0 hb' ⟨h1,h2⟩).mpr h3⟩


private theorem mod_add_congr_left {x y m : Nat} (h : x%m=y%m) (z : Nat) :
    (x+z)%m=(y+z)%m := by
  rw [Nat.add_mod x z, Nat.add_mod y z, h]

private theorem canonical_congr {a b n : Nat} : Z a b (n%(a+b)) ↔ Z a b n :=
  Z_congr (Nat.mod_mod _ _)

private theorem cycle_lambda {a b n : Nat} (ha : 0<a) (hab : a<b) :
    Lambda a b (n%(a+b)) ↔ ¬ Z a b n ∧ ¬ Z a b (n+a) := by
  let u := n%(a+b)
  have hu : u<a+b := Nat.mod_lt _ (by omega)
  have h0 : Z a b u ↔ Z a b n := canonical_congr
  have h1 : Z a b (u+a) ↔ Z a b (n+a) :=
    Z_congr (mod_add_congr_left (Nat.mod_mod _ _) _)
  change Lambda a b u ↔ _
  rw [← h0, ← h1]
  unfold Lambda
  by_cases hb : b≤u
  · have hZ : Z a b (u+a) := by
      rw [show u+a=(u-b)+(a+b) by omega, Z_period]
      exact Z_initial hab (by omega)
    simp [hZ, show ¬u<b by omega]
  · by_cases hd : b-a≤u
    · have hZ : ¬ Z a b (u+a) := by
        rw [Z_small (by omega : u+a<a+b)]
        omega
      simp [hd,hZ, show u<b by omega]
    · have hZ : Z a b (u+a) ↔ ¬ Z a b u := by
        rw [Z_small (by omega : u+a<a+b), Z_small hu]
        simp [show u+a<b by omega, show u<b by omega, flip ha]
      rw [hZ]
      simp [hd]

private theorem Lambda_imp_D {a b u : Nat} (hab : a<b) (h : Lambda a b u) :
    D a b u := by
  refine ⟨?_,h.2.1,h.2.2⟩
  by_cases hu : u<a
  · exact False.elim (h.2.2 (Z_initial hab hu))
  · omega

private theorem add_eq_of_mod {m x y r : Nat} (hx : x<m) (hy : y<m)
    (hs : (x+y)%m=r) : x+y=r ∨ x+y=r+m := by
  by_cases h : x+y<m
  · rw [Nat.mod_eq_of_lt h] at hs
    exact Or.inl hs
  · rw [Nat.mod_eq_sub_mod (by omega : m≤x+y),
      Nat.mod_eq_of_lt (by omega : x+y-m<m)] at hs
    exact Or.inr (by omega)

/-- Within the full blocks the reflection reverses the block number and its offset. -/
private theorem reflect_full {a b h x y : Nat} (ha : 0<a)
    (hB : 2*a*h+a≤b) (hphase : x%(2*a)<a)
    (hs : x+y=2*a*h+a-1) : Z a b y := by
  let k := x/(2*a)
  let t := x%(2*a)
  have he : t+2*a*k=x := Nat.mod_add_div _ _
  have hk : k≤h := by
    by_cases hh : k≤h
    · exact hh
    · have hm := mul_mono a (show h+1≤k by omega)
      rw [Nat.mul_succ] at hm
      omega
  have hmul := mul_mono a hk
  have hsub := Nat.mul_sub_left_distrib (2*a) h k
  have hy : y=2*a*(h-k)+(a-1-t) := by omega
  refine (Z_small (by omega)).mpr ⟨by omega,?_⟩
  rw [hy, phase_block (by omega : a-1-t<2*a)]
  omega

private theorem reflect_odd {a b h r x y : Nat} (ha : 0<a) (hr : r<a)
    (hb : b=2*a*h+a+r) (hx : x<a+b) (hy : y<a+b)
    (hs : (x+y)%(a+b)=2*a*h+a-1) (hz : Z a b x) : Z a b y := by
  obtain ⟨hxb,hxt⟩ := (Z_small hx).mp hz
  have hX : x<2*a*h+a := by
    by_cases hlt : x<2*a*h+a
    · exact hlt
    · have he : 2*a*h+(x-2*a*h)=x := by omega
      have hp := phase_block (a:=a) (k:=h) (t:=x-2*a*h) (by omega)
      rw [he] at hp
      omega
  rcases add_eq_of_mod hx hy hs with h | h
  · exact reflect_full ha (by omega) hxt h
  · omega

private theorem reflect_even {a b h r x y : Nat} (ha : 0<a) (hr : r<a)
    (hb : b=2*a*(h+1)+r) (hx : x<a+b) (hy : y<a+b)
    (hs : (x+y)%(a+b)=2*a*h+a-1) (hz : Z a b x) : Z a b y := by
  rw [Nat.mul_succ] at hb
  obtain ⟨hxb,hxt⟩ := (Z_small hx).mp hz
  by_cases hfull : x<2*a*h+a
  · rcases add_eq_of_mod hx hy hs with h | h
    · exact reflect_full ha (by omega) hxt h
    · omega
  · have hpartial : 2*a*(h+1)≤x := by
      rw [Nat.mul_succ]
      by_cases ht : x<2*a*h+2*a
      · have he : 2*a*h+(x-2*a*h)=x := by omega
        have hp := phase_block (a:=a) (k:=h) (t:=x-2*a*h) (by omega)
        rw [he] at hp
        omega
      · omega
    have hp' : 2*a*h+2*a≤x := by rwa [Nat.mul_succ] at hpartial
    have hsum : x+y=(2*a*h+a-1)+(a+b) := by
      rcases add_eq_of_mod hx hy hs with h | h
      · omega
      · exact h
    have hy' : y=2*a*(h+1)+(r-1-(x-2*a*(h+1))) := by
      rw [Nat.mul_succ]
      omega
    refine (Z_small hy).mpr ⟨by omega,?_⟩
    rw [hy', phase_block (by rw [Nat.mul_succ]; omega : r-1-(x-2*a*(h+1))<2*a)]
    omega

private theorem reflection_and_mirror {a b : Nat} (ha : 0<a) (hab : a<b) :
    ∃ R, R<a+b ∧
      (∀ x y, x<a+b → y<a+b → (x+y)%(a+b)=R → Z a b x → Z a b y) ∧
      (∀ v, Lambda a b v → ∃ u, Lambda a b u ∧ (u+v+a)%(a+b)=R) := by
  let q := b/a
  let r := b%a
  let h := q/2
  have hr : r<a := Nat.mod_lt _ ha
  have hb : r+a*q=b := Nat.mod_add_div b a
  have hq : q%2+2*h=q := Nat.mod_add_div q 2
  by_cases he : q%2=0
  · have hq' : q=2*h := by omega
    have hb' : b=2*a*h+r := by
      rw [hq', ← Nat.mul_assoc, Nat.mul_comm a 2] at hb
      omega
    have hh : 0<h := by
      by_cases h0 : h=0
      · rw [h0, Nat.mul_zero, Nat.zero_add] at hb'
        omega
      · exact Nat.pos_of_ne_zero h0
    let k := h-1
    have hb'' : b=2*a*(k+1)+r := by
      dsimp [k]
      rwa [show h-1+1=h by omega]
    let R := 2*a*k+a-1
    have hM : R<a+b := by dsimp [R]; rw [Nat.mul_succ] at hb''; omega
    refine ⟨R,hM,fun x y hx hy hs hz => reflect_even ha hr hb'' hx hy hs hz,?_⟩
    intro v hv
    obtain ⟨hl,hu⟩ := (Lambda_even hb'' hr).mp hv
    let u := (2*a*k+a+r)+(2*a*(k+1)-1-v)
    have hUb : 2*a*k+a+r≤u ∧ u<2*a*(k+1) := by
      dsimp [u]
      omega
    refine ⟨u,(Lambda_even hb'' hr).mpr hUb,?_⟩
    have hh' : u+v+a=R+(a+b) := by
      dsimp [u,R] at *
      rw [Nat.mul_succ] at hb'' hu ⊢
      omega
    rw [hh', Nat.add_mod_right, Nat.mod_eq_of_lt hM]
  · have hq' : q=2*h+1 := by omega
    have hb' : b=2*a*h+a+r := by
      rw [hq', Nat.mul_succ, ← Nat.mul_assoc, Nat.mul_comm a 2] at hb
      omega
    let R := 2*a*h+a-1
    have hM : R<a+b := by dsimp [R]; omega
    refine ⟨R,hM,fun x y hx hy hs hz => reflect_odd ha hr hb' hx hy hs hz,?_⟩
    intro v hv
    obtain ⟨hl,hu⟩ := (Lambda_odd hb' hr).mp hv
    let u := (2*a*h+a)+(b-1-v)
    have hUb : 2*a*h+a≤u ∧ u<b := by
      dsimp [u]
      omega
    refine ⟨u,(Lambda_odd hb' hr).mpr hUb,?_⟩
    have hh' : u+v+a=R+(a+b) := by dsimp [u,R]; omega
    rw [hh', Nat.add_mod_right, Nat.mod_eq_of_lt hM]

/-- Manabe's T2, directly expressed in terms of the residue rho. -/
def ManabeLongTest (a b c : Nat) : Prop :=
  let rho := c%(a+b)
  (∀ u, Lambda a b u → ¬ Z a b (rho+u)) ∧
    (∀ u, D a b u → ¬ Lambda a b ((rho+u)%(a+b)))

private theorem avoid_long_iff {a b c : Nat} (ha : 0<a) (hab : a<b) :
    LongTest a b c ↔ ManabeLongTest a b c := by
  let rho := c%(a+b)
  have hor (u : Nat) : (rho+u)%(a+b)=(c+u)%(a+b) :=
    mod_add_congr_left (Nat.mod_mod _ _) _
  change LongTest a b c ↔
    (∀ u, Lambda a b u → ¬ Z a b (rho+u)) ∧
    (∀ u, D a b u → ¬ Lambda a b ((rho+u)%(a+b)))
  constructor
  · intro h
    constructor
    · intro u hu hz
      exact no_move (Z_outcome ha hab) (by simp : a ∈ [a,b]) ha
        ((Z_congr (hor u)).mp hz) (h u hu)
    · intro u hu hv
      rw [hor u] at hv
      obtain ⟨R,_,hreflect,hmirror⟩ := reflection_and_mirror ha hab
      let v := (c+u)%(a+b)
      have hV : Lambda a b v := hv
      obtain ⟨w,hw,hs⟩ := hmirror v hV
      let x := (c+w+a)%(a+b)
      have hx : x<a+b := Nat.mod_lt _ (by omega)
      have huM : u<a+b := by unfold D at hu; omega
      have hzx : Z a b x := canonical_congr.mpr (h w hw)
      have hs' : (x+u)%(a+b)=R := calc
        (x+u)%(a+b) = ((c+w+a)+u)%(a+b) :=
          mod_add_congr_left (Nat.mod_mod _ _) _
        _ = ((c+u)+(w+a))%(a+b) := by congr 1; omega
        _ = (v+(w+a))%(a+b) :=
          mod_add_congr_left (Nat.mod_mod _ _).symm _
        _ = R := by rwa [show v+(w+a)=w+v+a by omega]
      exact hu.2.2 (hreflect x u hx huM hs' hzx)
  · rintro ⟨h1,h2⟩ u hu
    apply Classical.byContradiction
    intro hn
    have hD := Lambda_imp_D hab hu
    have hnot := h2 u hD
    rw [hor u] at hnot
    have hh := (cycle_lambda (n:=c+u) ha hab).mpr
      ⟨fun hz => h1 u hu ((Z_congr (hor u)).mpr hz),hn⟩
    exact hnot hh

/-- Manabe's T1, expressed without bounded-natural subtraction in the residue ring. -/
def ManabeMiddleTest (a b c : Nat) : Prop :=
  let rho := c%(a+b)
  ∀ x, x<b-a → Z a b x → ¬ Z a b (rho+x+(a+b)-(b-a))

private theorem avoid_middle_iff {a b c : Nat} (hbc : b<c) :
    MiddleTest a b c ↔ ManabeMiddleTest a b c := by
  let rho := c%(a+b)
  have he (x : Nat) : Z a b (c+x-(b-a)) ↔ Z a b (rho+x+(a+b)-(b-a)) := by
    have he1 : c+x-(b-a)+(a+b)=c+(x+((a+b)-(b-a))) := by omega
    have he2 : rho+x+(a+b)-(b-a)=rho+(x+((a+b)-(b-a))) := by omega
    rw [← Z_period a b (c+x-(b-a)), he1, he2]
    exact Z_congr (mod_add_congr_left (Nat.mod_mod _ _).symm _)
  exact ⟨fun h x hx hz hy => h x hx hz ((he x).mpr hy),
    fun h x hx hz hy => h x hx hz ((he x).mp hy)⟩

/-- A numerical value occurs among the legal options. -/
def GrundyOption (moves : List Nat) (g : Nat → Nat) (n v : Nat) : Prop :=
  ∃ s ∈ moves, 0<s ∧ s≤n ∧ g (n-s)=v

/-- The mex recurrence, in its characterization as the least missing natural. -/
def IsGrundy (moves : List Nat) (g : Nat → Nat) : Prop :=
  ∀ n, ¬ GrundyOption moves g n (g n) ∧
    ∀ v, v<g n → GrundyOption moves g n v

private theorem grundy_zero_outcome {moves : List Nat} {g : Nat → Nat}
    (hg : IsGrundy moves g) : IsOutcome moves (fun n => g n=0) := by
  intro n
  constructor
  · intro h s hm hs hn hz
    exact (hg n).1 ⟨s,hm,hs,hn,hz.trans h.symm⟩
  · intro h
    by_cases he : g n=0
    · exact he
    · obtain ⟨s,hm,hs,hn,hz⟩ := (hg n).2 0 (Nat.pos_of_ne_zero he)
      exact False.elim (h s hm hs hn hz)

def GrundyPeriod (g : Nat → Nat) (p : Nat) := ∀ n, g (n+p)=g n

def GrundyLeastPeriod (g : Nat → Nat) (p : Nat) :=
  0<p ∧ GrundyPeriod g p ∧ ∀ d, 0<d → GrundyPeriod g d → p≤d

private theorem outcome_period_of_grundy {a b c p : Nat} {g : Nat → Nat}
    (hg : IsGrundy [a,b,c] g) (hp : GrundyPeriod g p) :
    Period (Y a b c) p := by
  intro n
  have hh := unique_outcome (losing_outcome [a,b,c]) (grundy_zero_outcome hg)
  change Losing [a,b,c] (n+p) ↔ Losing [a,b,c] n
  rw [hh (n+p), hh n, hp n]

/-- The two implications of Manabe Conjecture 57. The result is stronger
    in that p is allowed to be any pure period, and no primitivity or
    non-additivity assumption is needed. -/
theorem manabe_conjecture_57 {a b c : Nat} {g : Nat → Nat}
    (ha : 0<a) (hab : a<b) (hbc : b<c) (hg : IsGrundy [a,b,c] g) :
    (GrundyPeriod g (c+a) → ManabeMiddleTest a b c) ∧
      (GrundyPeriod g (c+b) → ManabeLongTest a b c) := by
  constructor
  · intro hp
    exact (avoid_middle_iff hbc).mp ((period_middle_iff ha hab hbc).mp
      (outcome_period_of_grundy hg hp))
  · intro hp
    exact (avoid_long_iff ha hab).mp ((period_long_iff ha hab hbc).mp
      (outcome_period_of_grundy hg hp))

/-- Manabe Conjecture 57 in the published least-period formulation. -/
theorem manabe_conjecture_57_least {a b c p : Nat} {g : Nat → Nat}
    (ha : 1<a) (hab : a<b) (hbc : b<c) (_prim : a.gcd (b.gcd c)=1)
    (_nonadd : c≠a+b) (hg : IsGrundy [a,b,c] g) (hp : GrundyLeastPeriod g p) :
    (p=c+a → ManabeMiddleTest a b c) ∧ (p=c+b → ManabeLongTest a b c) := by
  obtain ⟨h1,h2⟩ := manabe_conjecture_57 (by omega) hab hbc hg
  constructor
  · intro he
    exact h1 (he ▸ hp.2.1)
  · intro he
    exact h2 (he ▸ hp.2.1)


private theorem least_missing_of_bound (values : List Nat) :
    ∃ m, m ∉ values ∧ ∀ v, v<m → v ∈ values := by
  classical
  have bound : ∀ (l : List Nat) v, v∈l → v≤l.foldr max 0 := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
      intro v hv
      rw [List.mem_cons] at hv
      rw [List.foldr_cons]
      rcases hv with he | hs
      · subst v
        exact Nat.le_max_left ..
      · exact Nat.le_trans (ih v hs) (Nat.le_max_right ..)
  obtain ⟨n,hn⟩ : ∃ n, n ∉ values :=
    ⟨values.foldr max 0+1, fun hv => by have := bound _ _ hv; omega⟩
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : ∃ v, v<n ∧ v ∉ values
    · obtain ⟨v,hv,hvm⟩ := h
      exact ih v hv hvm
    · refine ⟨n,hn,?_⟩
      intro v hv
      apply Classical.byContradiction
      exact fun hm => h ⟨v,hv,hm⟩

private noncomputable def mex (values : List Nat) : Nat :=
  Classical.choose (least_missing_of_bound values)

private theorem mex_spec (values : List Nat) :
    mex values ∉ values ∧ ∀ v, v<mex values → v ∈ values :=
  Classical.choose_spec (least_missing_of_bound values)

private def optionValues (moves : List Nat) (n : Nat)
    (value : ∀ s, (0<s ∧ s≤n) → Nat) : List Nat :=
  moves.filterMap fun s => if hs : 0<s ∧ s≤n then some (value s hs) else none

/-- The canonical Sprague–Grundy function obtained by applying mex at each heap. -/
noncomputable def Grundy (moves : List Nat) (n : Nat) : Nat :=
  mex (optionValues moves n fun s _hs => Grundy moves (n-s))
termination_by n
decreasing_by omega

private theorem mem_grundy_options (moves : List Nat) (n v : Nat) :
    v ∈ optionValues moves n (fun s _ => Grundy moves (n-s)) ↔
      GrundyOption moves (Grundy moves) n v := by
  rw [optionValues, List.mem_filterMap]
  constructor
  · rintro ⟨s,hm,he⟩
    by_cases hs : 0<s ∧ s≤n
    · exact ⟨s,hm,hs.1,hs.2,by simpa [hs] using he⟩
    · simp [hs] at he
  · rintro ⟨s,hm,hp,hl,hv⟩
    refine ⟨s,hm,?_⟩
    simp [show 0<s ∧ s≤n from ⟨hp,hl⟩, hv]

theorem grundy_is_grundy (moves : List Nat) : IsGrundy moves (Grundy moves) := by
  intro n
  let vals := optionValues moves n (fun s _ => Grundy moves (n-s))
  have hval : Grundy moves n=mex vals := by rw [Grundy]
  have hmem (v : Nat) : v ∈ vals ↔ GrundyOption moves (Grundy moves) n v :=
    mem_grundy_options moves n v
  have hs := mex_spec vals
  constructor
  · intro hg
    apply hs.1
    rw [← hval]
    exact (hmem _).mpr hg
  · intro v hv
    apply (hmem v).mp
    apply hs.2
    rwa [← hval]

/-- Manabe Conjecture 57 for the canonical mex sequence. -/
theorem manabe_conjecture_57_canonical {a b c p : Nat}
    (ha : 1<a) (hab : a<b) (hbc : b<c) (prim : a.gcd (b.gcd c)=1)
    (nonadd : c≠a+b) (hp : GrundyLeastPeriod (Grundy [a,b,c]) p) :
    (p=c+a → ManabeMiddleTest a b c) ∧ (p=c+b → ManabeLongTest a b c) :=
  manabe_conjecture_57_least ha hab hbc prim nonadd (grundy_is_grundy _) hp

/-- An eventual period of a purely periodic predicate is also a pure period. -/
theorem eventual_period_is_pure {f : Nat → Prop} {p q : Nat}
    (hq : 0<q) (pure : Period f q)
    (eventual : ∃ t, ∀ n, t≤n → (f (n+p) ↔ f n)) : Period f p := by
  obtain ⟨t, ht⟩ := eventual
  intro n
  have hqt : t≤q*t := by
    have h := Nat.mul_le_mul_right t hq
    simpa only [Nat.one_mul] using h
  have h := ht (n+q*t) (by omega)
  rw [show n+q*t+p=(n+p)+q*t by omega, period_add_mul pure, period_add_mul pure] at h
  exact h

/-- The article's two invariants, zero preperiod and least eventual period p. -/
def ZeroPreperiodLeastEventual (f : Nat → Prop) (p : Nat) :=
  0<p ∧ Period f p ∧
    ∀ d, 0<d → (∃ t, ∀ n, t≤n → (f (n+d) ↔ f n)) → p≤d

theorem least_pure_iff_zero_preperiod {f : Nat → Prop} {p : Nat} :
    LeastPeriod f p ↔ ZeroPreperiodLeastEventual f p := by
  constructor
  · rintro ⟨hpos,hper,hmin⟩
    exact ⟨hpos,hper,fun d hd he => hmin d hd (eventual_period_is_pure hpos hper he)⟩
  · rintro ⟨hpos,hper,hmin⟩
    exact ⟨hpos,hper,fun d hd he => hmin d hd ⟨0,fun n _ => he n⟩⟩

/-- Miklós–Post Conjecture 3 with its original zero-preperiod terminology. -/
theorem miklos_post_conjecture_3_original {a b c : Nat}
    (ha : 1<a) (hab : a<b) (hbc : b<c) :
    ZeroPreperiodLeastEventual (Y a b c) (b+c) ↔ MiklosPostTest a b c :=
  least_pure_iff_zero_preperiod.symm.trans
    (miklos_post_conjecture_3 (by omega) hab hbc)

theorem phase_iff_even_quotient {a n : Nat} (ha : 0<a) :
    n%(2*a)<a ↔ (n/a)%2=0 := by
  let q := n/a
  let r := n%a
  let h := q/2
  have hr : r<a := Nat.mod_lt _ ha
  have hn : r+a*q=n := Nat.mod_add_div n a
  have hq : q%2+2*h=q := Nat.mod_add_div q 2
  by_cases hh : q%2=0
  · have hq' : q=2*h := by omega
    rw [hq', ← Nat.mul_assoc, Nat.mul_comm a 2] at hn
    have he : n=2*a*h+r := by omega
    have hp : n%(2*a)=r := he.symm ▸ phase_block (by omega : r<2*a)
    change n%(2*a)<a ↔ q%2=0
    rw [hp]
    simp [hr,hh]
  · have hq' : q=2*h+1 := by omega
    rw [hq', Nat.mul_succ, ← Nat.mul_assoc, Nat.mul_comm a 2] at hn
    have he : n=2*a*h+(a+r) := by omega
    have hp : n%(2*a)=a+r := he.symm ▸ phase_block (by omega : a+r<2*a)
    change n%(2*a)<a ↔ q%2=0
    rw [hp]
    omega

#print axioms miklos_post_conjecture_3_original
#print axioms manabe_conjecture_57_canonical

end SubtractionPeriods
