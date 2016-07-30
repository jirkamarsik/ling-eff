open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Vec as Vec using (Vec) renaming (_∷_ to _,_; [] to ∅)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym; cong; trans)

module MyFin where

data Fin : (k : ℕ) → Set where
  zero : {k : ℕ} -> Fin (suc k)
  suc : {k : ℕ} -> Fin k -> Fin (suc k)

lookup : {k : ℕ} → {A : Set} → Fin k → Vec A k → A
lookup zero    (A , Γ) = A
lookup (suc n) (A , Γ) = lookup n Γ

natFin : {k : ℕ} → (n : ℕ) → Fin (suc (n) + k)
natFin zero    = zero
natFin (suc k) = suc (natFin k)

finNat : {k : ℕ} → Fin k → ℕ
finNat zero    = zero
finNat (suc k) = suc (finNat k)

lemma_sucFinNat : {k : ℕ} → {n : Fin k} → suc (finNat n) ≡ finNat (suc n)
lemma_sucFinNat = refl

lemma_sucNatFin : {k : ℕ} → {n : ℕ} → suc (natFin n) ≡ natFin {k} (suc n)
lemma_sucNatFin = refl

-- natFinNat : {k : ℕ} → {n : ℕ} → n ≡ finNat (natFin {k} n)
-- natFinNat {zero} = refl
-- natFinNat {suc n} = trans (trans (cong suc natFinNat) lemma_sucFinNat) lemma_sucNatFin

data Type : Set where
  ι : Type
  ο : Type
  _⇒_ : Type → Type → Type

data _⊢_ : {k : ℕ} → (Γ : Vec Type k) → (A : Type) → Set where
  var : {k : ℕ} → {Γ : Vec Type k} → (x : Fin k) → Γ ⊢ lookup x Γ
  abs : {A : Type} → {B : Type} → {k : ℕ} → {Γ : Vec Type k} → (A , Γ) ⊢ B → Γ ⊢ (A ⇒ B)
  app : {A : Type} → {B : Type} → {k : ℕ} → {Γ : Vec Type k} → Γ ⊢ (A ⇒ B) → Γ ⊢ A → Γ ⊢ B
