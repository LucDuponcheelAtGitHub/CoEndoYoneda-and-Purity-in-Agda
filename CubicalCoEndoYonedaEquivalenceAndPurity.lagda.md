# Cubical CoEndoYoneda Equivalence and Purity

```agda
{-# OPTIONS --cubical --guardedness #-}
module CubicalCoEndoYonedaEquivalenceAndPurity where
```

## Equivalence

### Set levels

First we need to `import` some library artifacts from Cubical Agda.

```agda
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
```

We use Cubical Agda's native equality `_≡_` and its native function extensionality `funExt`.
We also need function composition, `_•_`, and function identity, `idf`. 

```agda
_•_ : ∀ {ℓ1 ℓ2 ℓ3} {A : Type ℓ1} {B : A → Type ℓ2} {C : (a : A) → B a → Type ℓ3}
      (g : {a : A} (b : B a) → C a b) (f : (a : A) → B a) (a : A) → C a (f a)
g • f = λ x → g (f x)

idf : ∀ {ℓ} {A : Type ℓ} → A → A
idf x = x
```

We encode equivalence as two functions, `from` and `to`, that are each other's inverses.

```agda
record _⇿_ {ℓ ℓ' : Level} (A : Type ℓ) (B : Type ℓ') : Type (ℓ ⊔ ℓ') where
  field
    to : A → B
    from : B → A
    to_from : ∀ x → to (from x) ≡ x
    from_to : ∀ x → from (to x) ≡ x
```

To start with, we set the scene by encoding the standard coEndoYoneda equivalence in Cubical Agda.

```agda
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets

open Functor
open NatTrans
```

Cubical Agda provides function extensionality (`funExt`) and symmetry of equality (`sym`) natively.
The standard coEndoYoneda equivalence uses `SET ℓ`, which operates on sets `X : hSet ℓ` packaged with proofs
of their set-level truncation (`isSet`).

The standard coEndoYoneda equivalence has a set level that is one level higher than the set level
it is an equivalence about.

The standard coEndoYoneda equivalence is about the endofunctor, `Sets_CYEF`, of the category of
sets, `SET ℓ`, that, given an object `X`, maps every set `Y` to all morphisms, i.e. functions,
`fst X → fst Y` from `X` to `Y`.

```agda
record StandardCoEndoYonedaEquivalence {ℓ : Level} : Type (lsuc ℓ) where

  Sets_CYEF : hSet ℓ → Functor (SET ℓ) (SET ℓ)
  Sets_CYEF X = record
    { F-ob = λ Y → (fst X → fst Y) , isSetΠ (λ _ → snd Y)
    ; F-hom = λ f g x → f (g x)
    ; F-id = refl
    ; F-seq = λ f g → refl
    }
```

Given an endofunctor, `F : Functor (SET ℓ) (SET ℓ)`, and a set `X`, the standard coEndoYoneda
equivalence is an equivalence between the natural transformations from `Sets_CYEF X` to `F` and the
elements of `fst (F-ob F X)`.

This equivalence is the foundation of studying sets `X` by studying all functions `X → Y` to sets
`Y`. In Cubical Agda, equality of natural transformations follows directly from function
extensionality and paths, without needing extra postulates.

```agda
  module StandardEquivalence 
    (F : Functor (SET ℓ) (SET ℓ))
    (X : hSet ℓ) where

    τx2fx : NatTrans (Sets_CYEF X) F → fst (F-ob F X)
    τx2fx τx = N-ob τx X (λ x → x)

    fx2τx-η : fst (F-ob F X) → ∀ Y → (fst X → fst Y) → fst (F-ob F Y)
    fx2τx-η fx Y f = F-hom F f fx

    fx2τx : fst (F-ob F X) → NatTrans (Sets_CYEF X) F
    fx2τx fx = record
      { N-ob = fx2τx-η fx
      ; N-hom = λ {Y Z} f → funExt (λ g i → F-seq F {x = X} {y = Y} {z = Z} g f i fx)
      }

    from_to-τx2fx : ∀ (fx : fst (F-ob F X)) → τx2fx (fx2τx fx) ≡ fx
    from_to-τx2fx fx = funExt⁻ (F-id F) fx

    to_from-τx2fx : ∀ (τx : NatTrans (Sets_CYEF X) F) → fx2τx (τx2fx τx) ≡ τx
    to_from-τx2fx τx = makeNatTransPath (funExt (λ Y → funExt (λ f i → 
      N-hom τx {x = X} {y = Y} f (~ i) (λ x → x))))

    equivalence : (NatTrans (Sets_CYEF X) F) ⇿ (fst (F-ob F X))
    equivalence = record
      { to = τx2fx
      ; from = fx2τx
      ; to_from = from_to-τx2fx
      ; from_to = to_from-τx2fx
      }
```

## Standard CoYoneda Equivalence

```agda
module StandardCoYonedaEquivalence {ℓ ℓ' : Level} (C : Category ℓ ℓ') where
  private
    module C = Category C

  open C 

  CYF : C.ob → Functor C (SET ℓ')
  CYF X = record
    { F-ob = λ Y → C.Hom[ X , Y ] , C.isSetHom
    ; F-hom = λ f g → g ⋆ f
    ; F-id = funExt C.⋆IdR
    ; F-seq = λ f g → funExt (λ h → sym (C.⋆Assoc h f g))
    }

  module Equivalence 
    (F : Functor C (SET ℓ')) 
    (X : C.ob) where

    τx2fx : NatTrans (CYF X) F → fst (F-ob F X)
    τx2fx τx = N-ob τx X C.id

    fx2τx-η : fst (F-ob F X) → ∀ Y → (C.Hom[ X , Y ] → fst (F-ob F Y))
    fx2τx-η fx Y = λ f → F-hom F f fx

    fx2τx : fst (F-ob F X) → NatTrans (CYF X) F
    fx2τx fx = record
      { N-ob = fx2τx-η fx
      ; N-hom = λ {Y Z} f → funExt (λ g i → F-seq F {x = X} {y = Y} {z = Z} g f i fx)
      }

    from_to-τx2fx : ∀ (fx : fst (F-ob F X)) → τx2fx (fx2τx fx) ≡ fx
    from_to-τx2fx fx = funExt⁻ (F-id F) fx

    to_from-τx2fx : ∀ (τx : NatTrans (CYF X) F) → fx2τx (τx2fx τx) ≡ τx
    to_from-τx2fx τx = makeNatTransPath (funExt (λ Y → funExt (λ f → 
      sym (funExt⁻ (N-hom τx {x = X} {y = Y} f) C.id) ∙ cong (N-ob τx Y) (C.⋆IdL f))))

    equivalence : (NatTrans (CYF X) F) ⇿ (fst (F-ob F X))
    equivalence = record
      { to = τx2fx
      ; from = fx2τx
      ; to_from = from_to-τx2fx
      ; from_to = to_from-τx2fx
      }
```

## Basic Functional Category

```agda
record BasicFunctionalCategory
    {ℓ : Level}
    (C : Category (lsuc ℓ) ℓ) 
    (FF : Functor (SET ℓ) C) : Type (lsuc ℓ) where
  private
    module C = Category C
    module FF = Functor FF

  open C
  open StandardCoYonedaEquivalence C

  T : hSet ℓ
  T = Unit* , isSetUnit*

  t : fst T
  t = tt*

  CYEF : C.ob → Functor C C
  CYEF X = FF ∘F (CYF X)

  FFT : C.ob
  FFT = FF.F-ob T

  GEFF : Functor C C
  GEFF = CYEF FFT 

  field
    nu : NatTrans Id GEFF
    nu-eq-T : N-ob nu (FF.F-ob T) ≡ FF.F-hom (λ _ → FF.F-hom (λ _ → t))

  ηu : ∀ X → C.Hom[ X , F-ob GEFF X ]
  ηu = N-ob nu
```

## Functional Category

```agda
record FunctionalCategory 
    {ℓ : Level}
    (C : Category (lsuc ℓ) ℓ) 
    (FF : Functor (SET ℓ) C) : Type (lsuc ℓ) where
  private
    module C = Category C
    module FF = Functor FF

  open C
  open StandardCoYonedaEquivalence C

  field
    bfc : BasicFunctionalCategory C FF

  open BasicFunctionalCategory bfc public

  GFF : Functor C (SET ℓ)
  GFF = CYF FFT

  field
    nu-eq : ∀ {W : hSet ℓ} → N-ob nu (FF.F-ob W) ≡ FF.F-hom (λ w → FF.F-hom (λ _ → w))

    mu : NatTrans (GEFF ∘F GEFF) GEFF  

    monad-idˡ : ∀ {X} → N-ob nu (F-ob GEFF X) ⋆ N-ob mu X ≡ C.id

  ηm : ∀ X → C.Hom[ F-ob (GEFF ∘F GEFF) X , F-ob GEFF X ]
  ηm = N-ob mu
```

## CoEndoYoneda Equivalence

```agda
record CoEndoYonedaEquivalence 
    {ℓ : Level}
    (C : Category (lsuc ℓ) ℓ)
    (FF : Functor (SET ℓ) C) : Type (lsuc ℓ) where

  private
    module C = Category C
    module FF = Functor FF

  open C
  
  field
    fc : FunctionalCategory C FF

  open FunctionalCategory fc
  open StandardCoYonedaEquivalence C

  module CoEndoEquivalence {F : Functor C C} {X : C.ob} where
    private
      module F = Functor F
      module CYEF = Functor (CYEF X)
      
    G : Functor C C
    G = GEFF

    GG : Functor C (SET ℓ)
    GG = GFF ∘F GEFF
    
    private
      module G = Functor G
      module GG = Functor GG

    τx2ggfx : NatTrans (CYEF X) (G ∘F F) → fst (GG.F-ob (F.F-ob X))
    τx2ggfx τx = FF.F-hom (λ _ → C.id) ⋆ N-ob τx X

    ggfx2τx-η : fst (GG.F-ob (F.F-ob X)) → ∀ Y → C.Hom[ CYEF.F-ob Y , G.F-ob (F.F-ob Y) ]
    ggfx2τx-η ggfx Y = (FF.F-hom (λ f → ggfx ⋆ G.F-hom (F.F-hom f))) ⋆ ηm (F.F-ob Y)

    ggfx2τx-commute-lemma : 
      ∀ (ggfx : fst (GG.F-ob (F.F-ob X))) {Y Z : C.ob} (f : C.Hom[ Y , Z ]) (g : C.Hom[ X , Y ]) →
        ggfx ⋆ G.F-hom (F.F-hom (g ⋆ f)) ≡ (ggfx ⋆ G.F-hom (F.F-hom g)) ⋆ G.F-hom (F.F-hom f)
    ggfx2τx-commute-lemma ggfx {Y} {Z} f g = 
      ggfx ⋆ G.F-hom (F.F-hom (g ⋆ f))
        ≡⟨ cong (λ k → ggfx ⋆ k) (cong G.F-hom (F.F-seq g f)) ⟩
      ggfx ⋆ G.F-hom (F.F-hom g ⋆ F.F-hom f)
        ≡⟨ cong (λ k → ggfx ⋆ k) (G.F-seq (F.F-hom g) (F.F-hom f)) ⟩
      ggfx ⋆ (G.F-hom (F.F-hom g) ⋆ G.F-hom (F.F-hom f))
        ≡⟨ sym (C.⋆Assoc ggfx (G.F-hom (F.F-hom g)) (G.F-hom (F.F-hom f))) ⟩
      (ggfx ⋆ G.F-hom (F.F-hom g)) ⋆ G.F-hom (F.F-hom f)
        ∎

    ggfx2τx-commute : 
      ∀ (ggfx : fst (GG.F-ob (F.F-ob X))) {Y Z : C.ob} (f : C.Hom[ Y , Z ]) → 
        CYEF.F-hom f ⋆ ggfx2τx-η ggfx Z ≡ ggfx2τx-η ggfx Y ⋆ G.F-hom (F.F-hom f)
    ggfx2τx-commute ggfx {Y} {Z} f =
      let
        A = CYEF.F-hom f
        B_Z = FF.F-hom (λ g → ggfx ⋆ G.F-hom (F.F-hom g))
        B_Y = FF.F-hom (λ g → ggfx ⋆ G.F-hom (F.F-hom g))
        C_f = FF.F-hom (λ u → u ⋆ G.F-hom (F.F-hom f))
        
        
        
        step3 : FF.F-hom (λ g → ggfx ⋆ G.F-hom (F.F-hom (g ⋆ f))) ≡ 
                FF.F-hom (λ g → (ggfx ⋆ G.F-hom (F.F-hom g)) ⋆ G.F-hom (F.F-hom f))
        step3 = cong FF.F-hom (funExt (λ g → 
                  ggfx ⋆ G.F-hom (F.F-hom (g ⋆ f))
                    ≡⟨ cong (λ k → ggfx ⋆ k) (cong G.F-hom (F.F-seq g f)) ⟩
                  ggfx ⋆ G.F-hom (F.F-hom g ⋆ F.F-hom f)
                    ≡⟨ cong (λ k → ggfx ⋆ k) (G.F-seq (F.F-hom g) (F.F-hom f)) ⟩
                  ggfx ⋆ (G.F-hom (F.F-hom g) ⋆ G.F-hom (F.F-hom f))
                    ≡⟨ sym (C.⋆Assoc ggfx (G.F-hom (F.F-hom g)) (G.F-hom (F.F-hom f))) ⟩
                  (ggfx ⋆ G.F-hom (F.F-hom g)) ⋆ G.F-hom (F.F-hom f)
                    ∎))
        
        
        
        
      in 
        A ⋆ (B_Z ⋆ ηm (F.F-ob Z))
          ≡⟨ sym (C.⋆Assoc A B_Z (ηm (F.F-ob Z))) ⟩
        (A ⋆ B_Z) ⋆ ηm (F.F-ob Z)
          ≡⟨ cong (λ k → k ⋆ ηm (F.F-ob Z)) (sym (FF.F-seq (λ g → g ⋆ f) (λ h → ggfx ⋆ G.F-hom (F.F-hom h)))) ⟩
        FF.F-hom (λ g → ggfx ⋆ G.F-hom (F.F-hom (g ⋆ f))) ⋆ ηm (F.F-ob Z)
          ≡⟨ cong (λ k → k ⋆ ηm (F.F-ob Z)) step3 ⟩
        FF.F-hom (λ g → (ggfx ⋆ G.F-hom (F.F-hom g)) ⋆ G.F-hom (F.F-hom f)) ⋆ ηm (F.F-ob Z)
          ≡⟨ cong (λ k → k ⋆ ηm (F.F-ob Z)) (FF.F-seq (λ g → ggfx ⋆ G.F-hom (F.F-hom g)) (λ u → u ⋆ G.F-hom (F.F-hom f))) ⟩
        (B_Y ⋆ C_f) ⋆ ηm (F.F-ob Z)
          ≡⟨ C.⋆Assoc B_Y C_f (ηm (F.F-ob Z)) ⟩
        B_Y ⋆ (C_f ⋆ ηm (F.F-ob Z))
          ≡⟨ cong (λ k → B_Y ⋆ k) (N-hom mu (F.F-hom f)) ⟩
        B_Y ⋆ (ηm (F.F-ob Y) ⋆ G.F-hom (F.F-hom f))
          ≡⟨ sym (C.⋆Assoc B_Y (ηm (F.F-ob Y)) (G.F-hom (F.F-hom f))) ⟩
        (B_Y ⋆ ηm (F.F-ob Y)) ⋆ G.F-hom (F.F-hom f)
          ∎

    ggfx2τx : fst (GG.F-ob (F.F-ob X)) → NatTrans (CYEF X) (G ∘F F)
    ggfx2τx ggfx = record
      { N-ob = ggfx2τx-η ggfx
      ; N-hom = λ f → ggfx2τx-commute ggfx f
      }

    to_from-proof-lemma1 : ∀ (ggfx : fst (GG.F-ob (F.F-ob X))) → 
      ggfx ⋆ G.F-hom (F.F-hom C.id) ≡ ggfx ⋆ C.id
    to_from-proof-lemma1 ggfx = 
      ggfx ⋆ G.F-hom (F.F-hom C.id)
        ≡⟨ cong (λ k → ggfx ⋆ G.F-hom k) F.F-id ⟩
      ggfx ⋆ G.F-hom C.id
        ≡⟨ cong (λ k → ggfx ⋆ k) G.F-id ⟩
      ggfx ⋆ C.id
        ∎

    to_from-proof-lemma2 : ∀ (t : fst T) →
      FF.F-hom (λ (_ : fst T) → t) ≡ C.id
    to_from-proof-lemma2 t = 
      FF.F-hom (λ _ → t) 
        ≡⟨ cong FF.F-hom (funExt (λ x → refl)) ⟩
      FF.F-hom (λ x → x)
        ≡⟨ FF.F-id ⟩
      C.id
        ∎

    to_from-proof : ∀ (ggfx : fst (GG.F-ob (F.F-ob X))) → τx2ggfx (ggfx2τx ggfx) ≡ ggfx
    to_from-proof ggfx = 
      let
        A = FF.F-hom (λ _ → C.id)
        B = FF.F-hom (λ f → ggfx ⋆ G.F-hom (F.F-hom f))
      in 
        τx2ggfx (ggfx2τx ggfx)
          ≡⟨ sym (C.⋆Assoc A B (ηm (F.F-ob X))) ⟩
        (A ⋆ B) ⋆ ηm (F.F-ob X)
          ≡⟨ cong (λ k → k ⋆ ηm (F.F-ob X)) (sym (FF.F-seq (λ _ → C.id) (λ f → ggfx ⋆ G.F-hom (F.F-hom f)))) ⟩
        FF.F-hom (λ x → ggfx ⋆ G.F-hom (F.F-hom C.id)) ⋆ ηm (F.F-ob X)
          ≡⟨ cong (λ k → k ⋆ ηm (F.F-ob X)) (cong FF.F-hom (funExt (λ _ → to_from-proof-lemma1 ggfx))) ⟩
        FF.F-hom (λ _ → ggfx ⋆ C.id) ⋆ ηm (F.F-ob X)
          ≡⟨ cong (λ k → k ⋆ ηm (F.F-ob X)) (cong FF.F-hom (funExt (λ _ → C.⋆IdR ggfx))) ⟩
        FF.F-hom (λ _ → ggfx) ⋆ ηm (F.F-ob X)
          ≡⟨ cong (λ k → k ⋆ ηm (F.F-ob X)) (cong FF.F-hom (funExt (λ _ → sym (C.⋆IdL ggfx)))) ⟩
        FF.F-hom (λ t → C.id ⋆ ggfx) ⋆ ηm (F.F-ob X)
          ≡⟨ cong (λ k → k ⋆ ηm (F.F-ob X)) (cong FF.F-hom (funExt (λ t → cong (λ k → k ⋆ ggfx) (sym (to_from-proof-lemma2 t))))) ⟩
        FF.F-hom (λ t → FF.F-hom (λ _ → t) ⋆ ggfx) ⋆ ηm (F.F-ob X)
          ≡⟨ cong (λ k → k ⋆ ηm (F.F-ob X)) (FF.F-seq (λ t → FF.F-hom (λ _ → t)) (λ k → k ⋆ ggfx)) ⟩
        (FF.F-hom (λ t → FF.F-hom (λ _ → t)) ⋆ G.F-hom ggfx) ⋆ ηm (F.F-ob X)
          ≡⟨ C.⋆Assoc (FF.F-hom (λ t → FF.F-hom (λ _ → t))) (G.F-hom ggfx) (ηm (F.F-ob X)) ⟩
        FF.F-hom (λ t → FF.F-hom (λ _ → t)) ⋆ (G.F-hom ggfx ⋆ ηm (F.F-ob X))
          ≡⟨ cong (λ k → k ⋆ (G.F-hom ggfx ⋆ ηm (F.F-ob X))) (sym nu-eq-T) ⟩
        ηu FFT ⋆ (G.F-hom ggfx ⋆ ηm (F.F-ob X))
          ≡⟨ sym (C.⋆Assoc (ηu FFT) (G.F-hom ggfx) (ηm (F.F-ob X))) ⟩
        (ηu FFT ⋆ G.F-hom ggfx) ⋆ ηm (F.F-ob X)
          ≡⟨ cong (λ k → k ⋆ ηm (F.F-ob X)) (sym (N-hom nu ggfx)) ⟩
        (ggfx ⋆ ηu (G.F-ob (F.F-ob X))) ⋆ ηm (F.F-ob X)
          ≡⟨ C.⋆Assoc ggfx (ηu (G.F-ob (F.F-ob X))) (ηm (F.F-ob X)) ⟩
        ggfx ⋆ (ηu (G.F-ob (F.F-ob X)) ⋆ ηm (F.F-ob X))
          ≡⟨ cong (λ k → ggfx ⋆ k) monad-idˡ ⟩
        ggfx ⋆ C.id
          ≡⟨ C.⋆IdR ggfx ⟩
        ggfx
          ∎

    from_to-proof : ∀ (τx : NatTrans (CYEF X) (G ∘F F)) (Y : C.ob) → ggfx2τx-η (τx2ggfx τx) Y ≡ N-ob τx Y
    from_to-proof τx Y = 
      let
        A : C.Hom[ FFT , CYEF.F-ob X ]
        A = FF.F-hom (λ _ → C.id)
        B : C.Hom[ CYEF.F-ob X , G.F-ob (F.F-ob X) ]
        B = N-ob τx X
        C_f : C.Hom[ X , Y ] → C.Hom[ G.F-ob (F.F-ob X) , G.F-ob (F.F-ob Y) ]
        C_f = λ f → G.F-hom (F.F-hom f)
      in
        FF.F-hom (λ f → (A ⋆ B) ⋆ C_f f) ⋆ ηm (F.F-ob Y)
          ≡⟨ cong (λ k → k ⋆ ηm (F.F-ob Y)) (cong FF.F-hom (funExt (λ f → C.⋆Assoc A B (C_f f)))) ⟩
        FF.F-hom (λ f → A ⋆ (B ⋆ C_f f)) ⋆ ηm (F.F-ob Y)
          ≡⟨ cong (λ k → k ⋆ ηm (F.F-ob Y)) (cong FF.F-hom (funExt (λ f → cong (λ k → A ⋆ k) (sym (N-hom τx f))))) ⟩
        FF.F-hom (λ f → A ⋆ (CYEF.F-hom f ⋆ N-ob τx Y)) ⋆ ηm (F.F-ob Y)
          ≡⟨ cong (λ k → k ⋆ ηm (F.F-ob Y)) (cong FF.F-hom (funExt (λ f → sym (C.⋆Assoc A (CYEF.F-hom f) (N-ob τx Y))))) ⟩
        FF.F-hom (λ f → (A ⋆ CYEF.F-hom f) ⋆ N-ob τx Y) ⋆ ηm (F.F-ob Y)
          ≡⟨ cong (λ k → k ⋆ ηm (F.F-ob Y)) (cong FF.F-hom (funExt (λ f → cong (λ k → k ⋆ N-ob τx Y) (sym (FF.F-seq (λ _ → C.id) (λ g → g ⋆ f)))))) ⟩
        FF.F-hom (λ f → FF.F-hom (λ _ → C.id ⋆ f) ⋆ N-ob τx Y) ⋆ ηm (F.F-ob Y)
          ≡⟨ cong (λ k → k ⋆ ηm (F.F-ob Y)) (cong FF.F-hom (funExt (λ f → cong (λ k → FF.F-hom {x = T} k ⋆ N-ob τx Y) (funExt (λ _ → C.⋆IdL f))))) ⟩
        FF.F-hom (λ f → FF.F-hom (λ _ → f) ⋆ N-ob τx Y) ⋆ ηm (F.F-ob Y)
          ≡⟨ cong (λ k → k ⋆ ηm (F.F-ob Y)) (FF.F-seq (λ f → FF.F-hom (λ _ → f)) (λ k → k ⋆ N-ob τx Y)) ⟩
        (FF.F-hom (λ f → FF.F-hom (λ _ → f)) ⋆ G.F-hom (N-ob τx Y)) ⋆ ηm (F.F-ob Y)
          ≡⟨ C.⋆Assoc (FF.F-hom (λ f → FF.F-hom (λ _ → f))) (G.F-hom (N-ob τx Y)) (ηm (F.F-ob Y)) ⟩
        FF.F-hom (λ f → FF.F-hom (λ _ → f)) ⋆ (G.F-hom (N-ob τx Y) ⋆ ηm (F.F-ob Y))
          ≡⟨ cong (λ k → k ⋆ (G.F-hom (N-ob τx Y) ⋆ ηm (F.F-ob Y))) (sym (nu-eq {W = CYF X .F-ob Y})) ⟩
        ηu (CYEF.F-ob Y) ⋆ (G.F-hom (N-ob τx Y) ⋆ ηm (F.F-ob Y))
          ≡⟨ sym (C.⋆Assoc (ηu (CYEF.F-ob Y)) (G.F-hom (N-ob τx Y)) (ηm (F.F-ob Y))) ⟩
        (ηu (CYEF.F-ob Y) ⋆ G.F-hom (N-ob τx Y)) ⋆ ηm (F.F-ob Y)
          ≡⟨ cong (λ k → k ⋆ ηm (F.F-ob Y)) (sym (N-hom nu (N-ob τx Y))) ⟩
        (N-ob τx Y ⋆ ηu (G.F-ob (F.F-ob Y))) ⋆ ηm (F.F-ob Y)
          ≡⟨ C.⋆Assoc (N-ob τx Y) (ηu (G.F-ob (F.F-ob Y))) (ηm (F.F-ob Y)) ⟩
        N-ob τx Y ⋆ (ηu (G.F-ob (F.F-ob Y)) ⋆ ηm (F.F-ob Y))
          ≡⟨ cong (λ k → N-ob τx Y ⋆ k) (monad-idˡ {X = F.F-ob Y}) ⟩
        N-ob τx Y ⋆ C.id
          ≡⟨ C.⋆IdR (N-ob τx Y) ⟩
        N-ob τx Y
          ∎

    pointfree-equivalence : (NatTrans (CYEF X) (G ∘F F)) ⇿ fst (GG.F-ob (F.F-ob X))
    pointfree-equivalence = record
      { to = τx2ggfx
      ; from = ggfx2τx
      ; to_from = to_from-proof
      ; from_to = λ τx → makeNatTransPath (funExt (λ Y → from_to-proof τx Y))
      }
```

## Purity

We now define a standard `MonadOnSets`.

```agda
record MonadOnSets {ℓ : Level} : Type (lsuc ℓ) where
  field
    F₀ : hSet ℓ → hSet ℓ
    mPure : ∀ {X : hSet ℓ} → fst X → fst (F₀ X)
    mApply : ∀ {X Y : hSet ℓ} → (fst X → fst (F₀ Y)) → fst (F₀ X) → fst (F₀ Y)
    
    mApply-pure : 
      ∀ {X Y : hSet ℓ} {f : fst X → fst (F₀ Y)} {x : fst X} → 
        mApply {X} {Y} f (mPure {X} x) ≡ f x
    mPure-mApply : 
      ∀ {X : hSet ℓ} {mx : fst (F₀ X)} → mApply {X} {X} (mPure {X}) mx ≡ mx
    mApply-assoc : 
      ∀ {X Y Z : hSet ℓ} {f : fst X → fst (F₀ Y)} {g : fst Y → fst (F₀ Z)} 
        {mx : fst (F₀ X)} →
      mApply {Y} {Z} g (mApply {X} {Y} f mx) ≡ mApply {X} {Z} (λ x → mApply {Y} {Z} g (f x)) mx
    
  mMap : ∀ {X Y : hSet ℓ} → (fst X → fst Y) → fst (F₀ X) → fst (F₀ Y)
  mMap {X} {Y} f = mApply {X} {Y} (λ x → mPure {Y} (f x))
```

We can formulate the purity theorems inside a parameterized module over a given Monad on sets.
We prove that `KleisliFunctionalCategory` is structurally equivalent to `Idempotent`.

```agda
module PurityTheorems {ℓ : Level} (M : MonadOnSets {ℓ}) where
  open MonadOnSets M

  SetsObj = hSet ℓ

  record _⇔_ (A B : Type (lsuc ℓ)) : Type (lsuc ℓ) where
    field
      to : A → B
      from : B → A

  record Idempotent : Type (lsuc ℓ) where
    field
      idempotent : 
        {X : hSet ℓ} (mx : fst (F₀ X)) → 
          mMap {X} {F₀ X} (mPure {X}) mx ≡ mPure {F₀ X} mx

  open Idempotent
  
  Kleisli : Category (lsuc ℓ) ℓ
  Kleisli = record
    { ob = hSet ℓ
    ; Hom[_,_] = λ A B → fst A → fst (F₀ B)
    ; id = λ {A} → mPure {A}
    ; _⋆_ = λ {A B C} f g x → mApply {B} {C} g (f x)
    ; ⋆IdL = λ {A B} f → funExt (λ x → mApply-pure {A} {B} {f} {x})
    ; ⋆IdR = λ {A B} f → funExt (λ x → mPure-mApply {B})
    ; ⋆Assoc = λ {A B C D} f g h → funExt (λ x → mApply-assoc {B} {C} {D})
    ; isSetHom = λ {A B} → isSetΠ (λ _ → snd (F₀ B))
    }

  KF : Functor (SET ℓ) Kleisli
  KF = record
    { F-ob = λ X → X
    ; F-hom = λ {A B} f x → mPure {B} (f x)
    ; F-id = refl
    ; F-seq = λ {A B C} f g → funExt (λ x → sym (mApply-pure {B} {C}))
    }

  KleisliBasicFunctionalCategory : Type (lsuc ℓ)
  KleisliBasicFunctionalCategory = BasicFunctionalCategory Kleisli KF

  mPure-mMap-eq :
    ∀ {X : hSet ℓ} (mx : fst (F₀ X)) → 
      mMap {X} {F₀ X} (mPure {X}) mx ≡ 
        mApply {X} {F₀ X} (λ x → mPure {F₀ X} (mPure {X} x)) mx
  mPure-mMap-eq {X} mx = refl

  idempotent-equiv-kleisli-basic-functional-category : KleisliBasicFunctionalCategory ⇔ Idempotent
  idempotent-equiv-kleisli-basic-functional-category = record
    { to = λ kfc → record 
        { idempotent = λ {X} mx → 
            let
              open BasicFunctionalCategory kfc
              
              sigma-eval-lemma : ∀ {Z : SetsObj} (mz : fst (F₀ Z)) → 
                mApply {Z} {F-ob GEFF Z} (N-ob nu Z) mz ≡ mPure {F-ob GEFF Z} (λ _ → mz)
              sigma-eval-lemma {Z} mz = 
                let
                  f : fst T → fst (F₀ Z)
                  f = λ _ → mz
                  nat-tt : mApply {Z} {F-ob GEFF Z} (N-ob nu Z) mz ≡ mApply {F-ob GEFF T} {F-ob GEFF Z} (F-hom GEFF f) (N-ob nu T t)
                  nat-tt = cong (λ H → H t) (N-hom nu f)
                  
                  left-eq : mApply {F-ob GEFF T} {F-ob GEFF Z} (F-hom GEFF f) (N-ob nu T t) ≡ mPure {F-ob GEFF Z} (λ _ → mz)
                  left-eq = 
                    mApply {F-ob GEFF T} {F-ob GEFF Z} (F-hom GEFF f) (N-ob nu T t)
                      ≡⟨ cong (λ k → mApply {F-ob GEFF T} {F-ob GEFF Z} (F-hom GEFF f) (k t)) nu-eq-T ⟩
                    mApply {F-ob GEFF T} {F-ob GEFF Z} (F-hom GEFF f) (mPure {F-ob GEFF T} (λ _ → mPure {T} t))
                      ≡⟨ mApply-pure {F-ob GEFF T} {F-ob GEFF Z} {f = F-hom GEFF f} ⟩
                    F-hom GEFF f (λ _ → mPure {T} t)
                      ≡⟨ refl ⟩
                    mPure {F-ob GEFF Z} (λ u → mApply {T} {Z} f (mPure {T} t))
                      ≡⟨ cong (λ k → mPure {F-ob GEFF Z} (λ _ → k)) (mApply-pure {T} {Z} {f = f}) ⟩
                    mPure {F-ob GEFF Z} (λ _ → f t)
                      ≡⟨ refl ⟩
                    mPure {F-ob GEFF Z} (λ _ → mz)
                      ∎
                in nat-tt ∙ left-eq
              
              eval : fst (F₀ (F-ob GEFF X)) → fst (F₀ (F₀ X))
              eval mg = mApply {F-ob GEFF X} {F₀ X} (λ g → mPure {F₀ X} (g t)) mg

              idempotent-lemma : (x : fst X) → 
                mApply {F-ob GEFF X} {F₀ X} (λ g → mPure {F₀ X} (g t)) (N-ob nu X x) ≡ mPure {F₀ X} (mPure {X} x)
              idempotent-lemma x = 
                mApply {F-ob GEFF X} {F₀ X} (λ g → mPure {F₀ X} (g t)) (N-ob nu X x)
                  ≡⟨ sym (cong eval (mApply-pure {X} {F-ob GEFF X} {f = N-ob nu X})) ⟩
                eval (mApply {X} {F-ob GEFF X} (N-ob nu X) (mPure {X} x))
                  ≡⟨ cong eval (sigma-eval-lemma {X} (mPure {X} x)) ⟩
                eval (mPure {F-ob GEFF X} (λ _ → mPure {X} x))
                  ≡⟨ mApply-pure {F-ob GEFF X} {F₀ X} {f = λ g → mPure {F₀ X} (g t)} ⟩
                mPure {F₀ X} (mPure {X} x)
                  ∎


            in 
              mMap {X} {F₀ X} (mPure {X}) mx
                ≡⟨ mPure-mMap-eq {X} mx ⟩
              mApply {X} {F₀ X} (λ x → mPure {F₀ X} (mPure {X} x)) mx
                ≡⟨ sym (cong (λ k → mApply {X} {F₀ X} k mx) (funExt (λ x → idempotent-lemma x))) ⟩
              mApply {X} {F₀ X} (λ x → mApply {F-ob GEFF X} {F₀ X} (λ g → mPure {F₀ X} (g t)) (N-ob nu X x)) mx
                ≡⟨ sym (mApply-assoc {X} {F-ob GEFF X} {F₀ X}) ⟩
              eval (mApply {X} {F-ob GEFF X} (N-ob nu X) mx)
                ≡⟨ cong eval (sigma-eval-lemma {X} mx) ⟩
              eval (mPure {F-ob GEFF X} (λ _ → mx))
                ≡⟨ mApply-pure {F-ob GEFF X} {F₀ X} {f = λ g → mPure {F₀ X} (g t)} ⟩
              mPure {F₀ X} mx
                ∎
        }
    ; from = λ idem → 
        let
          T : hSet ℓ
          T = Unit* , isSetUnit*

          GM : (Z : SetsObj) → SetsObj
          GM Z = (fst T → fst (F₀ Z)) , isSetΠ (λ _ → snd (F₀ Z))

          σ-mApply-lemma :
            ∀ {Z : SetsObj} (mz : fst (F₀ Z)) →
              mApply {Z} {GM Z} (λ z → mPure {GM Z} (λ _ → mPure {Z} z)) mz ≡ 
                mPure {GM Z} (λ _ → mz)
          σ-mApply-lemma {Z} mz = 
            let 
              MZ = F₀ Z
              GMZ = GM Z
              gmz = λ (_ : fst T) → mz
              MGMZ = F₀ GMZ
              mz2mgmz = λ (mz : fst MZ) → mPure {GMZ} (λ _ → mz)
            in 
              mApply {Z} {GMZ} (λ (z : fst Z) → mPure {GMZ} (λ _ → mPure {Z} z)) mz
                ≡⟨ sym (cong 
                  (λ k → mApply {Z} {GMZ} k mz)
                    (funExt (λ z → mApply-pure {MZ} {GMZ} {f = mz2mgmz}))) ⟩
              mApply {Z} {GMZ} (λ z → mApply {MZ} {GMZ} mz2mgmz (mPure {MZ} (mPure {Z} z))) mz
                ≡⟨ sym (mApply-assoc {Z} {MZ} {GMZ}) ⟩
              mApply {MZ} {GMZ} mz2mgmz (mApply {Z} {MZ} (λ z → mPure {MZ} (mPure {Z} z)) mz)
                ≡⟨ cong (λ k → mApply {MZ} {GMZ} mz2mgmz k) (sym (mPure-mMap-eq {Z} mz)) ⟩
              mApply {MZ} {GMZ} mz2mgmz (mMap {Z} {MZ} (mPure {Z}) mz)
                ≡⟨ cong (λ k → mApply {MZ} {GMZ} mz2mgmz k) (idempotent idem mz) ⟩
              mApply {MZ} {GMZ} mz2mgmz (mPure {MZ} mz)
                ≡⟨ mApply-pure {MZ} {GMZ} {f = mz2mgmz} ⟩
              mPure {GMZ} (λ _ → mz)
                ∎
          comm : ∀ {X Y : SetsObj} (gmx2mx : fst X → fst (F₀ Y)) (x : fst X) → 
            mApply {Y} {GM Y} (λ z → mPure {GM Y} (λ _ → mPure {Y} z)) (gmx2mx x) ≡ 
              mApply {GM X} {GM Y}
                (λ z → mPure {GM Y} (λ u → mApply {X} {Y} gmx2mx (z u)))
                  (mPure {GM X} (λ _ → mPure {X} x))
          comm {X} {Y} gmx2mx x = 
            let 
              f-lemma : fst (GM X) → fst (F₀ (GM Y))
              f-lemma z = mPure {GM Y} (λ u → mApply {X} {Y} gmx2mx (z u))
              
            in 
              mApply {Y} {GM Y} (λ z → mPure {GM Y} (λ _ → mPure {Y} z)) (gmx2mx x)
                ≡⟨ σ-mApply-lemma {Y} (gmx2mx x) ⟩
              mPure {GM Y} (λ _ → gmx2mx x)
                ≡⟨ sym (cong (λ k → mPure {GM Y} (λ _ → k)) (mApply-pure {X} {Y} {f = gmx2mx})) ⟩
              mPure {GM Y} (λ u → mApply {X} {Y} gmx2mx (mPure {X} x))
                ≡⟨ sym (mApply-pure {GM X} {GM Y} {f = f-lemma}) ⟩
              mApply {GM X} {GM Y} f-lemma (mPure {GM X} (λ _ → mPure {X} x))
                ∎
        in
        record { nu = record 
                  { N-ob = λ X x → mPure {GM X} (λ _ → mPure {X} x)
                  ; N-hom = λ {X Y} f → funExt (λ x → comm {X} {Y} f x)
                  }
               ; nu-eq-T = refl
        }
    }
```

We now define `EnforcingPurity` which is equivalent with `Idempotent`.

```agda
  record EnforcingPurity : Type (lsuc ℓ) where
    field
      enforcingPurity : {X : hSet ℓ} (mx : fst (F₀ X)) → mApply {X} {F₀ X} (λ z → mPure {F₀ X} (mPure {X} z)) mx ≡ mPure {F₀ X} mx

  open EnforcingPurity

  idempotent-equiv-enforcing-purity : Idempotent ⇔ EnforcingPurity 
  idempotent-equiv-enforcing-purity = record 
    { to = λ i → record
          { enforcingPurity = λ {X} mx →
                mApply {X} {F₀ X} (λ z → mPure {F₀ X} (mPure {X} z)) mx
                  ≡⟨ sym (mPure-mMap-eq {X} mx) ⟩
                mMap {X} {F₀ X} (mPure {X}) mx
                  ≡⟨ idempotent i mx ⟩
                mPure {F₀ X} mx
              ∎
          }
    ; from = λ ep → record
          { idempotent = λ {X} mx →
                mMap {X} {F₀ X} (mPure {X}) mx
                  ≡⟨ mPure-mMap-eq {X} mx ⟩
                mApply {X} {F₀ X} (λ z → mPure {F₀ X} (mPure {X} z)) mx
                  ≡⟨ enforcingPurity ep mx ⟩
                mPure {F₀ X} mx
              ∎
          }
    }
```

`Singleton` defines what it means to be a singleton.

```agda
  Singleton : Type ℓ → Type ℓ
  Singleton A = (x y : A) → x ≡ y
```

The main result is encoded in `enforcing-purity-implies-pure-unit-eq`.

```agda
  T : hSet ℓ
  T = Unit* , isSetUnit*

  t : fst T
  t = tt*
```

```agda
  enforcing-purity-implies-pure-unit-eq : 
    EnforcingPurity → (mt : fst (F₀ T)) → mt ≡ mPure {T} t
  enforcing-purity-implies-pure-unit-eq ep mt =
    let 
      MT = F₀ T
      MMT = F₀ MT
      μT = mApply {MT} {T} (λ (w : fst MT) → mPure {T} t)
          
      lhs-inner : 
        ∀ x → mApply {MT} {T} (λ (w : fst MT) → mPure {T} t) (mPure {MT} (mPure {T} x)) ≡ mPure {T} t
      lhs-inner x = 
        mApply {MT} {T} (λ (w : fst MT) → mPure {T} t) (mPure {MT} (mPure {T} x))
          ≡⟨ mApply-pure {MT} {T} {f = λ (w : fst MT) → mPure {T} t} ⟩
        mPure {T} t
          ∎
      
      ⊤-is-singleton : (a b : fst T) → a ≡ b
      ⊤-is-singleton x y = refl
      
      lhs-eq : μT (mApply {T} {MT} (λ z → mPure {MT} (mPure {T} z)) mt) ≡ mt
      lhs-eq = 
        μT (mApply {T} {MT} (λ z → mPure {MT} (mPure {T} z)) mt)
          ≡⟨ mApply-assoc {T} {MT} {T} {f = λ z → mPure {MT} (mPure {T} z)} {g = λ (w : fst MT) → mPure {T} t} {mx = mt} ⟩
        mApply {T} {T} (λ x → mApply {MT} {T} (λ (w : fst MT) → mPure {T} t) (mPure {MT} (mPure {T} x))) mt
          ≡⟨ cong (λ k → mApply {T} {T} k mt) (funExt (λ x → lhs-inner x)) ⟩
        mApply {T} {T} (λ x → mPure {T} t) mt
          ≡⟨ cong (λ k → mApply {T} {T} (λ x → mPure {T} (k x)) mt) (funExt (λ x → sym (⊤-is-singleton t x))) ⟩
        mApply {T} {T} (λ x → mPure {T} x) mt
          ≡⟨ mPure-mApply ⟩
        mt
          ∎

      rhs-eq : μT (mApply {T} {MT} (λ z → mPure {MT} (mPure {T} z)) mt) ≡ mPure {T} t
      rhs-eq = 
        μT (mApply {T} {MT} (λ z → mPure {MT} (mPure {T} z)) mt)
          ≡⟨ cong μT (enforcingPurity ep mt) ⟩
        μT (mPure {MT} mt)
          ≡⟨ mApply-pure {MT} {T} {f = λ (w : fst MT) → mPure {T} t} {x = mt} ⟩
        mPure {T} t
          ∎

    in sym lhs-eq ∙ rhs-eq
```

## Examples

Here are some concrete examples.

They use `Triple` in order to disambiguate from `Monad`

```agda

open import Data.Maybe hiding (_>>=_)
open import Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Function.Base using (id; _∘_)

open import Cubical.Relation.Nullary
open import Cubical.Data.Empty

private
  variable
    u : Level

record Triple {u : Level} (M : Type u → Type u) : Type (lsuc u) where
  field
    pure : ∀ {X : Type u} → X → M X
    _>>=_ : ∀ {X Y : Type u} → M X → (X → M Y) → M Y

open Triple {{...}}

EnforcingPurityEq : ∀ {u} (M : Type u → Type u) ⦃ _ : Triple M ⦄ → Type (lsuc u)
EnforcingPurityEq {u} M = ∀ {X : Type u} (mx : M X) → (mx >>= (pure ∘ pure)) ≡ pure mx

instance
  TripleMaybe : ∀ {u} → Triple {u} Maybe
  TripleMaybe = record
    { pure = just
    ; _>>=_ = λ { nothing _ → nothing
                  ; (just x) f → f x
                  }
    }

maybe-not-pure : ∀ {u} → ¬ EnforcingPurityEq {u} Maybe
maybe-not-pure {u} h =
  let T = Lift u Unit
  in contradiction-from (h (nothing {A = T}))
  where
    T = Lift u Unit
    contradiction-from : _≡_ {A = Maybe (Maybe T)} nothing (just nothing) → ⊥
    contradiction-from p = transport (λ i → P (p i)) tt*
      where
        P : Maybe (Maybe T) → Type lzero
        P nothing = Unit*
        P (just _) = ⊥

instance
  TripleList : ∀ {u} → Triple {u} List
  TripleList = record
    { pure = λ x → x ∷ []
    ; _>>=_ = λ xs f → concatMap f xs
    }

list-not-pure : ∀ {u} → ¬ EnforcingPurityEq {u} List
list-not-pure {u} h =
  let T = Lift u Unit
      t = lift tt
  in contradiction-from (h (t ∷ t ∷ []))
  where
    T = Lift u Unit
    t = lift tt
    contradiction-from : 
      _≡_ {A = List (List T)} ((t ∷ []) ∷ (t ∷ []) ∷ []) ((t ∷ t ∷ []) ∷ []) → ⊥
    contradiction-from p = transport (λ i → P (p i)) tt*
      where
        P : List (List T) → Type lzero
        P (_ ∷ _ ∷ _) = Unit*
        P _ = ⊥

MyReader : ∀ {u} → Type u → Type u → Type u
MyReader R X = R → X

instance
  TripleReader : ∀ {u} {R : Type u} → Triple (MyReader R)
  TripleReader = record
    { pure = λ x _ → x
    ; _>>=_ = λ m f r → f (m r) r
    }

SingletonProp : ∀ {u} → Type u → Type u
SingletonProp A = (x y : A) → x ≡ y

reader-purity-implies : ∀ {u} (R : Type u) → EnforcingPurityEq (MyReader R) → SingletonProp R
reader-purity-implies R h r1 r2 =
  cong (λ f → f r1 r2) (h (λ r → r))

MyWriter : ∀ {u} → Type u → Type u → Type u
MyWriter W X = X × W

module WriterTriple {u : Level} (W : Type u) (e : W) (_∙_ : W → W → W) where
  
  instance
    TripleWriter : Triple (MyWriter W)
    TripleWriter = record
      { pure = λ x → (x , e)
      ; _>>=_ = λ mx f → let (y , w) = f (fst mx) in (y , snd mx ∙ w)
      }

  writer-purity-implies : EnforcingPurityEq (MyWriter W) → ∀ w → w ≡ e
  writer-purity-implies h w =
    sym (cong snd (cong fst (h (e , w))))

MyState : ∀ {u} → Type u → Type u → Type u
MyState S X = S → X × S

instance
  TripleState : ∀ {u} {S : Type u} → Triple (MyState S)
  TripleState = record
    { pure = λ x s → (x , s)
    ; _>>=_ = λ mx f s → let (x , s') = mx s in f x s'
    }

state-purity-implies : ∀ {u} (S : Type u) → EnforcingPurityEq (MyState S) → SingletonProp S
state-purity-implies S h s1 s2 =
  cong (λ f → fst (f s2)) (cong (λ f → fst (f s1)) (h (λ s → (s , s))))

MyCont : ∀ {u} → Type u → Type u → Type u
MyCont R X = (X → R) → R

instance
  TripleCont : ∀ {u} {R : Type u} → Triple (MyCont R)
  TripleCont = record
    { pure = λ x k → k x
    ; _>>=_ = λ mx f k → mx (λ x → f x k)
    }

cont-purity-implies : ∀ {u} (R : Type u) → EnforcingPurityEq (MyCont R) → SingletonProp R
cont-purity-implies R h r1 r2 =
  let m1 : MyCont R R
      m1 = λ _ → r1
  in cong (λ f → f (λ _ → r2)) (h m1)

-- `IO` simulated as `MyErrorState`
MyErrorState : ∀ {u} → Type u → Type u → Type u → Type u
MyErrorState E S X = S → (E × S) ⊎ (X × S)

instance
  TripleMyErrorState : ∀ {u} {E S : Type u} → Triple (MyErrorState E S)
  TripleMyErrorState {u} {E} {S} = record
    { pure = λ x w → inr (x , w)
    ; _>>=_ = bind
    }
    where
      bind : ∀ {X Y : Type u} → MyErrorState E S X → (X → MyErrorState E S Y) → MyErrorState E S Y
      bind mx f w = helper (mx w) f
        where
          helper : ∀ {X Y} → (E × S) ⊎ (X × S) → (X → MyErrorState E S Y) → (E × S) ⊎ (Y × S)
          helper (inl err) f = inl err
          helper (inr (x , w')) f = f x w'

my-io-not-pure : ∀ {u} {E S : Type u} (e : E) (s : S) → ¬ EnforcingPurityEq (MyErrorState E S)
my-io-not-pure {u} {E} {S} e s h =
  let m = λ s → inl (e , s)
  in contradiction-from (cong (λ f → f s) (h m))
  where
    contradiction-from : {m : MyErrorState E S (Lift u Unit)} → _≡_ {A = (E × S) ⊎ (MyErrorState E S (Lift u Unit) × S)} (inl (e , s)) (inr (m , s)) → ⊥
    contradiction-from p = transport (λ i → P (p i)) tt*
      where
        P : (E × S) ⊎ (MyErrorState E S (Lift u Unit) × S) → Type lzero
        P (inl _) = Unit*
        P (inr _) = ⊥
```

