import Mathlib.Computability.Reduce


#eval (Encodable.encode (Option.none : Option ℕ))
#eval (Encodable.encode (Option.some 0 : Option ℕ))

#print REPred

-- A non-empty recursively enumerable set is the image of a primitive recursive function
def PrimRecImage {β : Type} [Primcodable β] (B : Set β) :=
  ∃ (f : ℕ → β), Primrec f ∧ ∀ b, b ∈ B ↔ ∃ a, f a ∈ B


def boundedMin (f : ℕ → Bool) (n : ℕ) : ℕ :=
  List.idxOf true <| List.map f (List.range n)

@[simp]
lemma boundedMin_zero (f : ℕ → Bool) :
  boundedMin f 0 = 0 :=
by
  unfold boundedMin
  simp [List.idxOf, List.range, List.range.loop]

-- lemma idxOf_concat (f : ℕ → Bool) (n m : ℕ

#print List.range.loop
lemma range.aux (n : ℕ) (l : List ℕ) :
  List.range.loop n l =
  List.range n ++ l :=
by
  revert l
  induction n <;> intro l
  case zero =>
    unfold List.range.loop
    simp [List.map, List.range.loop]
  case succ n ih =>
    simp [List.range, List.range.loop]
    rw [ih]
    rw [ih]; simp [List.map, List.append_assoc]


#print List.range'

@[simp]
lemma range_succ (n : ℕ) :
  List.range (n+1) = List.range n ++ [n] :=
by
  unfold List.range
  simp [List.range.loop]
  apply range.aux


lemma range_range' (n m : ℕ) :
  List.range (n + m) = List.range n ++ List.range' n m :=
by
  revert n
  induction m
  case zero =>
    simp [List.range, List.range.loop, List.range']
  case succ m ih =>
    intro n
    simp [List.range', List.range.loop]
    have h : (n + (m + 1)) = (n + 1) + m := by
      omega
    rw [h, ih]
    simp

#print List.findIdx.go

lemma idxOf_cons₁ {α} [BEq α][ReflBEq α] (a : α) (l : List α) :
  List.idxOf a (a :: l) = 0 :=
by
  simp [List.idxOf, List.findIdx, List.findIdx.go]

lemma findIdx_aux {α} (f : α → Bool) (n m : ℕ) (l : List α) :
  List.findIdx.go f l (n + m) = (List.findIdx.go f l n) + m :=
  by
  revert n m
  induction l
  case nil =>
    unfold List.findIdx.go
    simp [List.findIdx, List.findIdx.go]
  case cons a l ih =>
    simp [List.findIdx.go]
    cases (f a)
    case true =>
      simp
    case false =>
      intro n m
      simp [List.findIdx, List.findIdx.go]
      have h : (n + m + 1) = (n + 1) + m := by
        omega
      rw [h, ih]

lemma idxOf_cons₂ {α} [BEq α][LawfulBEq α] (a b : α) (l : List α) :
  a ≠ b →
  List.idxOf a (b :: l) = (List.idxOf a l) + 1 :=
by
  intro h
  have h : b ≠ a := by symm; trivial
  simp [List.idxOf, List.findIdx, List.findIdx.go]
  rw [← beq_eq_false_iff_ne] at h
  rw [h]
  have h : 1 = (0 + 1) := by
    omega
  rw (occs := .pos [1]) [h]; rw [findIdx_aux]
  simp


lemma idxOf_concat₁ {α} [BEq α] [LawfulBEq α] (a : α) (l₁ l₂ : List α) :
  a ∈ l₁ →
  List.idxOf a (l₁ ++ l₂) = List.idxOf a l₁ :=
by
  revert l₂
  induction l₁ <;> intro l₂
  case nil =>
    unfold List.idxOf
    simp [List.append_nil]
  case cons b l ih =>
    simp
    intro h; cases h
    case inl h =>
      rw [h, idxOf_cons₁]; simp [idxOf_cons₁]
    case inr h =>
      by_cases h: (a = b)
      case pos => rw [h, idxOf_cons₁]; simp [idxOf_cons₁]
      case neg =>
      rw [idxOf_cons₂]; any_goals trivial
      rw [idxOf_cons₂]; rw [ih]; trivial
      trivial


lemma idxOf_concat₂ {α} [BEq α] [LawfulBEq α] (a : α) (l₁ l₂ : List α) :
  a ∉ l₁ →
  List.idxOf a (l₁ ++ l₂) = l₁.length + List.idxOf a l₂ :=
by
  revert l₂
  induction l₁
  case nil =>
    unfold List.idxOf
    simp [List.append_nil]
  case cons b l ih =>
    simp; intros l₂ neq notin
    rw [idxOf_cons₂]; swap; trivial
    rw [ih]; omega; trivial



#eval boundedMin (fun x => x == 5) 10
#eval boundedMin (fun x => x == 12) 10

theorem Primrec.boundedMinPrimrec (f : ℕ → Bool) :
  Primrec f →
  Primrec (boundedMin f) :=
  by
    intro primrec_f
    unfold boundedMin
    apply Primrec.comp
    . apply Primrec₂.comp
      . apply Primrec.list_idxOf
      . apply Primrec.const
      . apply Primrec.id
    . apply Primrec.comp
      . apply Primrec.list_map
        . apply Primrec.id
        . refine comp₂ primrec_f Primrec₂.right
      . exact list_range

def boundedMinOpt (f : ℕ → Bool) (n : ℕ) : Option ℕ :=
  let idx := boundedMin f n
  if idx < n then some idx else none

lemma boundedMinRfind_mem (f : ℕ → Bool) (bound n : ℕ) :
  n ∈ Nat.rfind f →
  n < bound →
  true ∈ List.map f (List.range bound) :=
by
  revert n
  simp
  induction bound
  case zero =>
    intro n h
    simp [Nat.rfind, List.range]
  case succ bound ih =>
    intros n; intros; exists n


lemma boundedMinRfind (f : ℕ → Bool) (bound n : ℕ) :
  n ∈ Nat.rfind f →
  n < bound →
  boundedMin f bound = n :=
by
  intros mem; have mem' := mem; revert mem
  simp
  induction bound
  case zero =>
    intro _ _ _
    omega
  case succ bound ih =>
    intro h1 h2 lt
    simp [boundedMin]
    have lt_case: n < bound ∨ n = bound := by
      omega
    cases lt_case
    case inl lt =>
      rw [idxOf_concat₁]
      . apply ih <;> trivial
      . apply boundedMinRfind_mem <;> trivial
    case inr eq =>
      rw [idxOf_concat₂]
      . rw [← eq, h1]; simp
      . simp; intros m ltm; apply h2; omega

lemma boundedMinOptRfind (f : ℕ → Bool) (bound n : ℕ) :
  n ∈ Nat.rfind f →
  n < bound →
  boundedMinOpt f bound = .some n :=
by
  intros mem lt
  simp [boundedMinOpt]
  have h1 := boundedMinRfind f bound n mem lt
  constructor; omega; trivial

theorem Primrec.boundedMinOptPrimrec (f : ℕ → Bool) :
  Primrec f →
  Primrec (boundedMinOpt f) :=
  by
    intro primrec_f
    unfold boundedMinOpt
    apply Primrec.ite
    . apply Primrec₂.comp (f := λ x y ↦ decide <| x < y) (g := boundedMin f) (h := id)
      . apply Primrec.nat_lt
      . apply Primrec.boundedMinPrimrec; trivial
      . apply Primrec.id
    . apply Primrec.comp
      . apply Primrec.option_some
      . apply Primrec.boundedMinPrimrec; trivial
    . apply Primrec.const

#print Nat.Primrec
#print Nat.Partrec

-- Let's do this with codes: we associate a primitive recursive evaluator.

#print Nat.Partrec.Code
#print Nat.Partrec.Code.eval
#check Nat.Partrec.Code.exists_code

open Nat.Partrec (Code)

def evalPrim : Code → ℕ → ℕ → Option ℕ
| .zero, _, _ => some 0
| .succ, _, n => some (n + 1)
| .left, _, n => some n.unpair.1
| .right, _, n => some n.unpair.2
| .pair f g, bound, n =>
  Nat.pair <$> evalPrim f bound n <*> evalPrim g bound n
| .comp f g, bound, n =>
  evalPrim g bound n >>= evalPrim f bound
| .prec f g, bound, n =>
  Nat.unpaired (fun a m =>
    Nat.rec (evalPrim f bound a)
    (fun y IH ↦ do
      let i ← IH
      evalPrim g bound (Nat.pair a (Nat.pair y i)))
    m) n
| .rfind' f, bound, a =>
  boundedMinOpt
    (fun n => Option.isSome (do
      let v ← evalPrim f bound (Nat.pair a n)
      guard (v = 0)
      return v))
    bound


-- Crucial lemma
lemma evalCorrect (c : Code) (bound n out : ℕ) : evalPrim c bound n = .some out → out ∈ Code.eval c n :=
by
  revert bound n out
  induction c
  case zero =>
    intros bound n out h
    simp [evalPrim] at h
    cases h
    simp [Code.eval, pure, PFun.pure]
  case succ =>
    intros bound n out h
    simp [evalPrim] at h
    cases h
    simp [Code.eval]
  case left =>
    intros bound n out h
    simp [evalPrim] at h
    cases h
    simp [Code.eval]
  case right =>
    intros bound n out h
    simp [evalPrim] at h
    cases h
    simp [Code.eval]
  case pair f g f_ih g_ih =>
    intros bound n out h
    simp [evalPrim] at h
    match fh: (evalPrim f bound n) with
    | .none =>
      rw [fh] at h
      simp [Seq.seq] at h
    | .some x =>
      match gh: (evalPrim g bound n) with
      | .none => rw [gh] at h; simp [Seq.seq] at h
      | .some y =>
        rw [fh, gh] at h; simp [Seq.seq] at h
        simp [Code.eval, Seq.seq]
        exists x; constructor; apply f_ih; assumption
        exists y; constructor; apply g_ih <;> assumption
        assumption
  case comp f g f_ih g_ih =>
    intros bound n out h
    simp [evalPrim] at h
    simp [Code.eval]
    match gh: (evalPrim g bound n) with
    | .none =>
      rw [gh] at h
      simp at h
    | .some x =>
      rw [gh] at h; simp at h
      match fh: (evalPrim f bound x) with
      | .none => rw [fh] at h; simp [Seq.seq] at h
      | .some y =>
        rw [fh] at h; simp [Seq.seq] at h; rw [← h]
        exists x; constructor; apply g_ih; assumption
        apply f_ih; assumption
  case prec f g f_ih g_ih =>
    intros bound n out h
    simp [evalPrim] at h
    sorry
  case rfind' f f_ih =>
    intros bound n out h
    simp [evalPrim] at h
    simp [Code.eval]
    sorry

-- And evalPrim is primrec
lemma evalPrimPrimrec (c : Code) : Primrec₂ <| evalPrim c := sorry

theorem REPred_is_Primrec {α : Type} [Primcodable α] (A : Set α) (nonEmpty : A.Nonempty) :
  REPred A → PrimRecImage A
:=
by
  . sorry

#print Nat.Primrec

theorem Primrec_is_RE {α : Type} [Primcodable α] (f : ℕ → ℕ) (primrec_f : Nat.Primrec f) :
  ∃ f', Nat.Partrec f' ∧ ∀ n, (f' n).Dom ∧ (f n) ∈ f' n :=
by
  cases primrec_f
  case zero => exact ⟨pure 0,
    by
      constructor
      . apply Nat.Partrec.zero
      . intros n; simp [pure, PFun.pure]
  ⟩
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry

theorem Primrec_image_is_REPred {α β : Type} [Primcodable α] [Primcodable β]
  (B : Set β) (isIPrimrecImage : PrimRecImage B) :
  REPred B :=
by
  simp [REPred]
  have ⟨f, ⟨prf, h⟩⟩ := isIPrimrecImage
  sorry
