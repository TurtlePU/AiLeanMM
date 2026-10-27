-- Задачки для самостоятельного решения.
-- Задания легко найти, потому что настроенный
-- плагин для Lean 4 будет подсвечивать жёлтым
-- все использования sorry, которые я оставил
-- в качестве заглушек вместо решений.

-- STLC содержится в Lean как подсистема
namespace STLC
  variable (P Q R : Prop)

  theorem simplification : P → (Q → P) :=
    fun p _ => p

  theorem distribution :
    (P → Q → R) → (P → Q) → P → R :=
    fun f g p => f p (g p)

  -- Не доказывается. Подумайте, почему.
  theorem pierce's_law :
    ((P → Q) → P) → P :=
    fun f => sorry

  -- Переведите вывод из конспекта на Lean:
  theorem composition :
    (Q → R) → (P → Q) → P → R := sorry
end STLC

-- В Lean есть квантор всеобщности
namespace CoC
  -- Prop - тип "всех утверждений", т.е. типов,
  -- которые при теоретико-множественной
  -- семантике интерпретируются как
  -- утверждения.
  --
  -- Тогда можно определить ложное утверждение
  -- как то, из которого следует любое другое,
  -- используя тип всех утверждений и квантор
  -- всеобщности.
  def bottom : Prop := ∀ (P : Prop), P
  notation "⊥" => bottom

  def implication : Prop → Prop → Prop :=
    fun P Q => forall (_ : P), Q

  theorem ex_falso_quodlibet :
    forall (P : Prop), ⊥ → P :=
    fun P b => b P

  def not : Prop → Prop :=
    fun P => P → ⊥

  notation "~" P => not P

  def top : Prop := ∀ (P : Prop), P → P
  notation "⊤" => top

  theorem indeed : ⊤ := fun _ p => p

  def and : Prop → Prop → Prop :=
    fun P Q => forall (R : Prop),
      (P → Q → R) → R
  infixl:55 " ⊓ " => and

  theorem and_intro :
    forall (P Q : Prop),
    P → Q → P ⊓ Q :=
    fun _ _ p q _ f => f p q

  theorem proj_1 :
    forall (P Q : Prop), P ⊓ Q → P :=
    fun _ _ pq => pq _ (fun p _ => p)

  -- Завершите доказательство:
  theorem proj_2 :
    forall (P Q : Prop), P ⊓ Q → Q := sorry

  def equiv : Prop → Prop → Prop :=
    fun P Q => (P → Q) ⊓ (Q → P)

  infixl:35 " ≡ " => equiv

  def or : Prop → Prop → Prop :=
    fun P Q => ∀ (R : Prop), (P → R) → (Q → R) → R
  infixl:45 " ⊔ " => or

  -- Завершите доказательство:
  theorem by_left : forall P Q, P → P ⊔ Q :=
    sorry

  -- Завершите доказательство:
  theorem by_right : forall P Q, Q → P ⊔ Q :=
    sorry

  -- Завершите доказательство:
  theorem cases :
    forall (P Q R : Prop),
    (P → R) → (Q → R) → P ⊔ Q → R :=
    sorry

  -- Попробуйте завершить доказательство.
  -- Подумайте, в чём проблема.
  theorem de_morgan_1 :
    forall (P Q : Prop), ~ (P ⊓ Q) ≡ ~ P ⊔ ~ Q :=
    sorry

  -- Попробуйте завершить доказательство.
  -- Подумайте, в чём проблема.
  theorem de_morgan_2 :
    forall (P Q : Prop), ~ (P ⊔ Q) ≡ ~ P ⊓ ~ Q :=
    sorry
end CoC

#check (Prop : Type) -- Type = Type 0
#check (Type : Type 1)
#check (Type 1 : Type 2)

-- Индуктивное определение множества
-- натуральных чисел. Обратите внимание
-- на схожесть с нотацией Бэкуса-Наура!
inductive nat : Type
  | zero : nat
  | suc : nat → nat

def add : nat → nat → nat :=
  fun m n => match m with
  | nat.zero => n
  | nat.suc m => nat.suc (add m n)

def sub : nat → nat → nat :=
  fun m n => match m, n with
  | m, nat.zero => m
  | nat.zero, nat.suc _ => nat.zero
  | nat.suc m', nat.suc n' => sub m' n'

-- Определение равенства
-- между натуральными числами.
inductive eq : nat -> nat -> Prop
  -- Чем-то похоже на введение правила вывода.
  | refl : ∀ n, eq n n
infixl:35 " ≡ " => eq

def one : nat := nat.suc nat.zero
def two : nat := nat.suc one

theorem onePlusOneIsTwo : add one one ≡ two
  := eq.refl two

#eval (add (nat.suc nat.zero) (nat.suc nat.zero))

-- 0 + n = n:
theorem zeroPlus : ∀ n, add nat.zero n ≡ n :=
  fun n => eq.refl n

-- Если a=b, то f(a)=f(b)
theorem cong : ∀ (a b : nat) (f : nat → nat),
  a ≡ b → f a ≡ f b :=
  fun a _ f p => match p with
  | eq.refl _ => eq.refl (f a)

-- n + 0 = n:
theorem plusZero : ∀ n, add n nat.zero ≡ n :=
  fun n => match n with
  | nat.zero => eq.refl nat.zero
  | nat.suc n => cong _ _ nat.suc (plusZero n)

-- Завершите доказательство:
theorem assoc : ∀ k m n,
  add k (add m n) ≡ add (add k m) n :=
  fun k m n => match k with
  | nat.zero => sorry
  | nat.suc k => sorry
