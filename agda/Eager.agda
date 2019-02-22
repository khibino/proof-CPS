module Eager where

open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; ∃-syntax)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (yes; no; ¬_; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
import Relation.Binary.PropositionalEquality as E


data Ty : Set where
  ty-nat  : Ty
  ty-bool : Ty
  _⟶_   : Ty → Ty → Ty

{-
eqTy : (x y : Ty) → Dec (x ≡ y)
eqTy ty-nat ty-bool     =  no (λ ())
eqTy ty-bool ty-nat     =  no (λ ())
eqTy ty-nat (_ ⟶ _)   =  no (λ ())
eqTy (_ ⟶ _) ty-nat   =  no (λ ())
eqTy ty-bool (_ ⟶ _)  =  no (λ ())
eqTy (_ ⟶ _) ty-bool  =  no (λ ())
eqTy ty-nat ty-nat      =  yes refl
eqTy ty-bool ty-bool    =  yes refl
eqTy (x₁ ⟶ x₂) (y₁ ⟶ y₂) with eqTy x₁ y₁ | eqTy x₂ y₂
... | yes e₁ | yes e₂   =  yes (E.cong₂ _⟶_ e₁ e₂)
... | yes e₁ | no ¬e₂   =  no (λ { refl → ¬e₂ refl })
... | no ¬e₁ | _        =  no (λ { refl → ¬e₁ refl })
 -}

id : Set
id = ℕ

-- tm

data tm : Set where
  tm-nat  : ℕ → tm
  tm-bool : Bool → tm
  tm-var  : id → tm
  tm-abs  : id → Ty → tm → tm
  tm-app  : tm → tm → tm
  tm-if   : tm → tm → tm → tm

subst-syntax : tm → id → tm → tm
subst-syntax v x = subst
  where
    subst : tm → tm
    subst (tm-nat v)       = tm-nat v
    subst (tm-bool b)      = tm-bool b
    subst (tm-var x₁) with x ≟ x₁
    ...  | yes p           = v
    ...  | no ¬p           = tm-var x₁
    subst (tm-abs x₁ T t) with x ≟ x₁
    ...  | yes p           = tm-abs x₁ T t
    ...  | no ¬p           = tm-abs x₁ T (subst t)
    subst (tm-app t₁ t₂)   = tm-app (subst t₁) (subst t₂)
    subst (tm-if t₁ t₂ t₃) = tm-if (subst t₁) (subst t₂) (subst t₃)

syntax subst-syntax v x = ⟦ v / x ⟧

data value : tm → Set where
  v-nat  : (n : ℕ) → value (tm-nat n)
  v-bool : (b : Bool) → value (tm-bool b)
  v-abs  : (vn : id) → (T : Ty) → (body : tm) → value (tm-abs vn T body)

data _⟹_ : tm → tm → Set where
  st-abs  : ∀ v x t T →
            value v        →   -- eager
            tm-app (tm-abs x T t) v ⟹ ⟦ v / x ⟧ t
  st-app₁ : ∀ t₁ t₁' t₂ →
            t₁ ⟹ t₁'       →
            tm-app t₁ t₂ ⟹ tm-app t₁' t₂
  st-app₂ : ∀ t₁ t₂ t₂' →
            t₂ ⟹ t₂'       →
            tm-app t₁ t₂ ⟹ tm-app t₁ t₂'
  st-then : ∀ t₂ t₃ →
            tm-if (tm-bool true)  t₂ t₃ ⟹ t₂
  st-else : ∀ t₂ t₃ →
            tm-if (tm-bool false) t₂ t₃ ⟹ t₃
  st-if   : ∀ t₁ t₁' t₂ t₃ →
            t₁ ⟹ t₁'          →
            tm-if t₁ t₂ t₃ ⟹ tm-if t₁' t₂ t₃

-- step-example-1 : tm-app

-- partial-map type
pm : Set → Set
pm A = id → Maybe A

empty : ∀ {A} → pm A
empty  _ = nothing

-- extend
extend : ∀ {A} → pm A → id → A → pm A
extend Γ x T y with y ≟ x
...  | yes _ = just T
...  | no  _ = Γ y

extend-eq :
  {A : Set} →
  (Γ : pm A) → (x : id) → (T : A) →
  extend Γ x T x ≡ just T
extend-eq Γ x T with x ≟ x
extend-eq Γ x T | yes _ = refl
extend-eq Γ _ T | no n  = ⊥-elim (n refl)

extend-neq :
  {A : Set} →
  (Γ : pm A) → (x : id) → (T : A) →
  (y : id) →
   y ≢ x    →
  extend Γ x T y ≡ Γ y
extend-neq Γ x T y ne with y ≟ x
... | yes p = ⊥-elim (ne p)
... | no _  = refl

-- has-type
data _⊢_∶_ : pm Ty → tm → Ty → Set where
  ht-nat   : ∀ Γ n →
             Γ ⊢ tm-nat n ∶ ty-nat
  ht-bool  : ∀ Γ b →
             Γ ⊢ tm-bool b ∶ ty-bool
  ht-var   : ∀ Γ x T →
              Γ x ≡ just T →
              Γ ⊢ tm-var x ∶ T
  ht-abs   : ∀ Γ x U T t →
             extend Γ x U ⊢ t ∶ T →
             Γ ⊢ tm-abs x U t ∶ (U ⟶ T)
  ht-app   : ∀ Γ S T t₁ t₂ →
             Γ ⊢ t₁  ∶ (S ⟶ T) →
             Γ ⊢ t₂  ∶ S           →
             Γ ⊢ tm-app t₁ t₂ ∶ T
  ht-if    : ∀ Γ T t₁ t₂ t₃ →
             Γ ⊢ t₁ ∶ ty-bool    →
             Γ ⊢ t₂ ∶ T          →
             Γ ⊢ t₃ ∶ T          →
             Γ ⊢ tm-if t₁ t₂ t₃ ∶ T

var-a : ℕ
var-a = 0

typing-example-1 :
  empty ⊢ (tm-abs var-a ty-bool (tm-var var-a)) ∶ (ty-bool ⟶ ty-bool)
typing-example-1 =
  ht-abs empty var-a ty-bool ty-bool (tm-var var-a)
  (ht-var (extend empty var-a ty-bool) var-a ty-bool (extend-eq empty var-a ty-bool))

data appears-free-in : id → tm → Set where
  afi-var  : ∀ x →
             appears-free-in x (tm-var x)
  afi-app₁ : ∀ x t₁ t₂ →
             appears-free-in x t₁ →
             appears-free-in x (tm-app t₁ t₂)
  afi-app₂ : ∀ x t₁ t₂ →
             appears-free-in x t₂ →
             appears-free-in x (tm-app t₁ t₂)
  afi-abs  : ∀ x y T₁₁ t₁₂ →
             x ≢ y →
             appears-free-in x t₁₂ →
             appears-free-in x (tm-abs y T₁₁ t₁₂)
  afi-if   : ∀ x t₁ t₂ t₃ →
             appears-free-in x t₁ →
             appears-free-in x (tm-if t₁ t₂ t₃)
  afi-then : ∀ x t₁ t₂ t₃ →
             appears-free-in x t₂ →
             appears-free-in x (tm-if t₁ t₂ t₃)
  afi-else : ∀ x t₁ t₂ t₃ →
             appears-free-in x t₃ →
             appears-free-in x (tm-if t₁ t₂ t₃)

closed : tm → Set
closed t = ∀ x → ¬ appears-free-in x t

free-in-context : ∀ x t T Γ     →
                  appears-free-in x t →
                  Γ ⊢ t ∶ T          →
                  (∃[ T' ] (Γ x ≡ just T'))
free-in-context x .(tm-var x)         T            Γ (afi-var .x)                  (ht-var .Γ .x .T e)
  =  T , e
free-in-context x .(tm-app t₁ t₂)     T            Γ (afi-app₁ .x t₁ t₂ fi)        (ht-app .Γ T₁₁ .T .t₁ .t₂ htₐ ht₂)
  =  free-in-context x t₁  (T₁₁ ⟶ T) Γ fi htₐ
free-in-context x .(tm-app t₁ t₂)     T            Γ (afi-app₂ .x t₁ t₂ fi)        (ht-app .Γ T₁₁ .T .t₁ .t₂ htₐ ht₂)
  =  free-in-context x t₂  T₁₁         Γ fi ht₂
free-in-context x .(tm-abs y S t)     .(S ⟶ T)   Γ (afi-abs .x y S t ¬eq fi)     (ht-abs .Γ .y .S T .t ht) rewrite E.sym (extend-neq Γ y S x ¬eq)
  =  free-in-context x t T             (extend Γ y S) fi ht
free-in-context x .(tm-if t₁ t₂ t₃)   T            Γ (afi-if .x t₁ t₂ t₃ fi)      (ht-if .Γ .T .t₁ .t₂ .t₃ ht₁ ht₂ ht₃)
  =  free-in-context x t₁  ty-bool     Γ fi ht₁
free-in-context x .(tm-if t₁ t₂ t₃)   T            Γ (afi-then .x t₁ t₂ t₃ fi)    (ht-if .Γ .T .t₁ .t₂ .t₃ ht₁ ht₂ ht₃)
  =  free-in-context x t₂  T           Γ fi ht₂
free-in-context x .(tm-if t₁ t₂ t₃)   T            Γ (afi-else .x t₁ t₂ t₃ fi)    (ht-if .Γ .T .t₁ .t₂ .t₃ ht₁ ht₂ ht₃)
  =  free-in-context x t₃  T           Γ fi ht₃

-- corollary
typable-empty-closed :
  ∀ t T    →
  empty ⊢ t ∶ T →
  closed t
typable-empty-closed t T ht x afi with free-in-context x t T empty afi ht
typable-empty-closed t T ht x afi | _ , ()  --- nothing ≡ just _
