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
#print Nat.Partrec.Code.evaln
#check Nat.Partrec.Code.evaln_prim
#check Nat.Partrec.Code.exists_code

open Nat.Partrec (Code)

#check Code.evaln

-- enumCode₂
def enumCode₂ (c : Code) (mem : ℕ) (gas input : ℕ) : ℕ :=
  Option.casesOn (Code.evaln gas c input) mem (fun _ => input)

#check Option.rec
#check Primrec.option_casesOn
#check Primrec.pair

lemma enumCode_prim (c : Code) (mem : ℕ) :
  Primrec₂ (enumCode₂ c mem) := by
  simp [Primrec₂, enumCode₂]
  apply Primrec.option_casesOn ?_ ?_ ?_
  . refine (Code.evaln_prim).comp (.pair (.pair ?_ ?_) ?_)
    . exact Primrec.fst
    . exact Primrec.const c
    . exact Primrec.snd
  . exact Primrec.const mem
  . exact Primrec.snd.comp (Primrec.fst)

#check Code.eval_eq_rfindOpt
#check Code.evaln_complete
#print Nat.rfindOpt
#check Nat.rfindOpt_spec

lemma enumCode_image_aux (c : Code) (mem : ℕ) :
  ∀ k ∈ c.eval.Dom, ∃ gas, enumCode₂ c mem gas k = k :=
by
  intros k k_mem_dom
  simp [enumCode₂]
  have h := @Code.evaln_complete c k ((c.eval k).get k_mem_dom)
  simp at h
  have h' := h.1 ?_
  . have ⟨gas, h'⟩ := h'
    exists gas; simp [h']
  . exact Part.get_mem k_mem_dom

lemma enumCode_image_inc₂ (c : Code) (mem : ℕ) :
  ∀ n ∈ c.eval.Dom, ∃ p : ℕ, enumCode₂ c mem p.unpair.1 p.unpair.2 = n :=
  by
    intros n n_in_dom
    have ⟨gas, h⟩ := enumCode_image_aux c mem n n_in_dom
    exists Nat.pair gas n; simp; trivial


lemma enumCode_inc_image₂ (c : Code) (mem : ℕ) :
  mem ∈ c.eval.Dom →
  ∀ p : ℕ , enumCode₂ c mem p.unpair.1 p.unpair.2 ∈ (c.eval).Dom :=
  by
    intros mem_in_dom p
    simp [enumCode₂] at *
    cases h:(Code.evaln p.unpair.1 c p.unpair.2)
    case none => simpa
    case some val =>
      simp
      have h' := @Code.evaln_complete c p.unpair.2 val
      exists val; apply h'.2; exists p.unpair.1

def enumCode (c : Code)(mem k : ℕ) :=
  enumCode₂ c mem (k.unpair.1) (k.unpair.2)

theorem enumcode_iff_in_image (c : Code) (mem : ℕ)
(mem_in_dom : mem ∈ c.eval.Dom) (n : ℕ):
 n ∈ c.eval.Dom ↔ ∃ k, enumCode c mem k = n :=
 by
  apply Iff.intro
  case mp =>
    intros n_mem
    apply enumCode_image_inc₂; trivial
  case mpr =>
    -- this is dumb, how do I intro and destruct?
    intros h
    have ⟨k, h⟩ := h; rw [← h]
    apply enumCode_inc_image₂; trivial

open Encodable Part

#print Encodable

-- Some tedium here since we're not in ℕ
theorem REPred_is_Primrec {α : Type} [Primcodable α] (A : Set α) (nonEmpty : A.Nonempty) :
  REPred A → PrimRecImage A
:=
by
  simp [REPred, PrimRecImage]
  let f a := Part.assert (A a) (λ _ ↦ Part.some ())
  have eq_f : f = λ a ↦ Part.assert (A a) (λ _ ↦ Part.some ()) :=
    by eq_refl
  rw [← eq_f]; intros prf
  let f' : ℕ →. ℕ := fun n => Part.bind (decode (α := α) n) fun a => (f a).map encode
  have partRec_f' : Nat.Partrec f' := prf
  have h := Code.exists_code.1 partRec_f'
  have ⟨c, h⟩ := h
  let a := nonEmpty.choose
  have a_in_A : A a := by simp [a]; apply Exists.choose_spec
  have a_in_fDom : () ∈ f a := by simp [f]; trivial
  have enc_a_in_f' : 0 ∈ f' (encode a) := by simp [f']; exists ()
  let f'' k : α :=
    let x := enumCode c (encode a) k >>= decode (α := α)
    Option.casesOn x a (λ a' ↦ a')
  exists f''
  apply And.intro
  . sorry -- ugh
  . intro b
    sorry

#print Nat.Primrec

theorem Primrec_is_RE {α : Type} [Primcodable α] (f : ℕ → ℕ) (primrec_f : Nat.Primrec f) :
  ∃ f', Nat.Partrec f' ∧ ∀ n, (f' n).Dom ∧ (f n) ∈ f' n :=
by
  sorry

theorem Primrec_image_is_REPred {α β : Type} [Primcodable α] [Primcodable β]
  (B : Set β) (isIPrimrecImage : PrimRecImage B) :
  REPred B :=
by
  simp [REPred]
  have ⟨f, ⟨prf, h⟩⟩ := isIPrimrecImage
  sorry
