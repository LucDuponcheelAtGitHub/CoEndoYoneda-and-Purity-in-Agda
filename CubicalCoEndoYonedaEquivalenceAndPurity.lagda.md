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
The standard coEndoYoneda equivalence uses `SET ℓ`, which operates on sets `X : hSet ℓ` packaged with proofs of their set-level truncation (`isSet`).

The standard coEndoYoneda equivalence has a set level that is one level higher than the set level
it is an equivalence about.

The standard coEndoYoneda equivalence is about the endofunctor, `Sets_CYEF`, of the category of
sets, `SET ℓ`, that, given an object `X`, maps every set `Y` to all morphisms, i.e. functions, `fst X → fst Y` from `X` to `Y`.

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

Given an endofunctor, `F : Functor (SET ℓ) (SET ℓ)`, and a set `X`, the standard coEndoYoneda equivalence is an equivalence between the natural transformations from `Sets_CYEF X` to `F` and the elements of `fst (F-ob F X)`.

This equivalence is the foundation of studying sets `X` by studying all functions `X → Y` to sets `Y`. In Cubical Agda, equality of natural transformations follows directly from function extensionality and paths, without needing extra postulates.

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
    ; F-hom = λ f g → C._⋆_ g f
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

    monad-idˡ : ∀ {X} → C._⋆_ (N-ob nu (F-ob GEFF X)) (N-ob mu X) ≡ C.id

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
    τx2ggfx τx = _⋆_ (FF.F-hom (λ _ → C.id)) (N-ob τx X)

    ggfx2τx-η : fst (GG.F-ob (F.F-ob X)) → ∀ Y → C.Hom[ CYEF.F-ob Y , G.F-ob (F.F-ob Y) ]
    ggfx2τx-η ggfx Y = _⋆_ (FF.F-hom (λ f → _⋆_ ggfx (G.F-hom (F.F-hom f)))) (ηm (F.F-ob Y))

    ggfx2τx-commute : 
      ∀ (ggfx : fst (GG.F-ob (F.F-ob X))) {Y Z : C.ob} (f : C.Hom[ Y , Z ]) → 
        _⋆_ (CYEF.F-hom f) (ggfx2τx-η ggfx Z) ≡ _⋆_ (ggfx2τx-η ggfx Y) (G.F-hom (F.F-hom f))
    ggfx2τx-commute ggfx {Y} {Z} f =
      let
        A = CYEF.F-hom f
        B_Z = FF.F-hom (λ g → _⋆_ ggfx (G.F-hom (F.F-hom g)))
        B_Y = FF.F-hom (λ g → _⋆_ ggfx (G.F-hom (F.F-hom g)))
        C_f = FF.F-hom (λ u → _⋆_ u (G.F-hom (F.F-hom f)))
        
        step1 : _⋆_ A (_⋆_ B_Z (ηm (F.F-ob Z))) ≡ _⋆_ (_⋆_ A B_Z) (ηm (F.F-ob Z))
        step1 = sym (C.⋆Assoc A B_Z (ηm (F.F-ob Z)))
        
        step2 : _⋆_ A B_Z ≡ FF.F-hom (λ g → _⋆_ ggfx (G.F-hom (F.F-hom (_⋆_ g f))))
        step2 = sym (FF.F-seq (λ g → _⋆_ g f) (λ h → _⋆_ ggfx (G.F-hom (F.F-hom h))))
        
        step3 : FF.F-hom (λ g → _⋆_ ggfx (G.F-hom (F.F-hom (_⋆_ g f)))) ≡ 
                FF.F-hom (λ g → _⋆_ (_⋆_ ggfx (G.F-hom (F.F-hom g))) (G.F-hom (F.F-hom f)))
        step3 = cong FF.F-hom (funExt (λ g → 
                  let 
                    inner1 : F.F-hom (_⋆_ g f) ≡ _⋆_ (F.F-hom g) (F.F-hom f)
                    inner1 = F.F-seq g f
                    
                    inner2 : G.F-hom (F.F-hom (_⋆_ g f)) ≡ G.F-hom (_⋆_ (F.F-hom g) (F.F-hom f))
                    inner2 = cong G.F-hom inner1
                    
                    inner3 : G.F-hom (_⋆_ (F.F-hom g) (F.F-hom f)) ≡ _⋆_ (G.F-hom (F.F-hom g)) (G.F-hom (F.F-hom f))
                    inner3 = G.F-seq (F.F-hom g) (F.F-hom f)
                    
                    inner4 : _⋆_ ggfx (G.F-hom (F.F-hom (_⋆_ g f))) ≡ _⋆_ ggfx (_⋆_ (G.F-hom (F.F-hom g)) (G.F-hom (F.F-hom f)))
                    inner4 = cong (λ k → _⋆_ ggfx k) (inner2 ∙ inner3)
                    
                    inner5 : _⋆_ ggfx (_⋆_ (G.F-hom (F.F-hom g)) (G.F-hom (F.F-hom f))) ≡ _⋆_ (_⋆_ ggfx (G.F-hom (F.F-hom g))) (G.F-hom (F.F-hom f))
                    inner5 = sym (C.⋆Assoc ggfx (G.F-hom (F.F-hom g)) (G.F-hom (F.F-hom f)))
                  in inner4 ∙ inner5))
        
        step4 : FF.F-hom (λ g → _⋆_ (_⋆_ ggfx (G.F-hom (F.F-hom g))) (G.F-hom (F.F-hom f))) ≡ _⋆_ B_Y C_f
        step4 = FF.F-seq (λ g → _⋆_ ggfx (G.F-hom (F.F-hom g))) (λ u → _⋆_ u (G.F-hom (F.F-hom f)))
        
        step5 : _⋆_ (_⋆_ B_Y C_f) (ηm (F.F-ob Z)) ≡ _⋆_ B_Y (_⋆_ C_f (ηm (F.F-ob Z)))
        step5 = C.⋆Assoc B_Y C_f (ηm (F.F-ob Z))
        
        step6 : _⋆_ C_f (ηm (F.F-ob Z)) ≡ _⋆_ (ηm (F.F-ob Y)) (G.F-hom (F.F-hom f))
        step6 = N-hom mu (F.F-hom f)
        
        step7 : _⋆_ B_Y (_⋆_ (ηm (F.F-ob Y)) (G.F-hom (F.F-hom f))) ≡ _⋆_ (_⋆_ B_Y (ηm (F.F-ob Y))) (G.F-hom (F.F-hom f))
        step7 = sym (C.⋆Assoc B_Y (ηm (F.F-ob Y)) (G.F-hom (F.F-hom f)))
      in step1 ∙ (cong (λ k → _⋆_ k (ηm (F.F-ob Z))) (step2 ∙ (step3 ∙ step4)) ∙ (step5 ∙ (cong (λ k → _⋆_ B_Y k) step6 ∙ step7)))

    ggfx2τx : fst (GG.F-ob (F.F-ob X)) → NatTrans (CYEF X) (G ∘F F)
    ggfx2τx ggfx = record
      { N-ob = ggfx2τx-η ggfx
      ; N-hom = λ f → ggfx2τx-commute ggfx f
      }

    to_from-proof : ∀ (ggfx : fst (GG.F-ob (F.F-ob X))) → τx2ggfx (ggfx2τx ggfx) ≡ ggfx
    to_from-proof ggfx = 
      let
        A = FF.F-hom (λ _ → C.id)
        B = FF.F-hom (λ f → ggfx ⋆ G.F-hom (F.F-hom f))
        
        step1 : (A ⋆ B) ⋆ ηm (F.F-ob X) ≡ τx2ggfx (ggfx2τx ggfx)
        step1 = C.⋆Assoc A B (ηm (F.F-ob X))
        
        step2 : A ⋆ B ≡ FF.F-hom (λ x → ggfx ⋆ G.F-hom (F.F-hom C.id))
        step2 = sym (FF.F-seq (λ _ → C.id) (λ f → ggfx ⋆ G.F-hom (F.F-hom f)))
        
        step3 : FF.F-hom (λ x → ggfx ⋆ G.F-hom (F.F-hom C.id)) ≡ FF.F-hom (λ _ → ggfx ⋆ C.id)
        step3 = cong FF.F-hom (funExt (λ _ → cong (λ k → ggfx ⋆ G.F-hom k) F.F-id ∙ cong (λ k → ggfx ⋆ k) G.F-id))
        
        step4 : FF.F-hom (λ _ → ggfx ⋆ C.id) ≡ FF.F-hom (λ _ → ggfx)
        step4 = cong FF.F-hom (funExt (λ _ → C.⋆IdR ggfx))
        
        step5 : FF.F-hom (λ _ → ggfx) ≡ FF.F-hom (λ t → C.id ⋆ ggfx)
        step5 = cong FF.F-hom (funExt (λ _ → sym (C.⋆IdL ggfx)))
        
        step6 : FF.F-hom (λ t → C.id ⋆ ggfx) ≡ FF.F-hom (λ t → FF.F-hom (λ _ → t) ⋆ ggfx)
        step6 = cong FF.F-hom (funExt (λ t → cong (λ k → k ⋆ ggfx) (sym (
                  let 
                    inner1 : (λ (_ : fst T) → t) ≡ (λ x → x)
                    inner1 = funExt (λ x → refl)
                    inner2 : FF.F-hom (λ _ → t) ≡ FF.F-hom (λ x → x)
                    inner2 = cong FF.F-hom inner1
                    inner3 : FF.F-hom (λ x → x) ≡ C.id
                    inner3 = FF.F-id
                  in inner2 ∙ inner3
                ))))
        
        step7 : FF.F-hom (λ t → FF.F-hom (λ _ → t) ⋆ ggfx) ≡ FF.F-hom (λ t → FF.F-hom (λ _ → t)) ⋆ G.F-hom ggfx
        step7 = FF.F-seq (λ t → FF.F-hom (λ _ → t)) (λ k → k ⋆ ggfx)
        
        step8 : (FF.F-hom (λ t → FF.F-hom (λ _ → t)) ⋆ G.F-hom ggfx) ⋆ ηm (F.F-ob X) ≡ 
                FF.F-hom (λ t → FF.F-hom (λ _ → t)) ⋆ (G.F-hom ggfx ⋆ ηm (F.F-ob X))
        step8 = C.⋆Assoc (FF.F-hom (λ t → FF.F-hom (λ _ → t))) (G.F-hom ggfx) (ηm (F.F-ob X))
        
        step9 : FF.F-hom (λ t → FF.F-hom (λ _ → t)) ≡ ηu FFT
        step9 = sym nu-eq-T
        
        step10 : ηu FFT ⋆ (G.F-hom ggfx ⋆ ηm (F.F-ob X)) ≡ (ηu FFT ⋆ G.F-hom ggfx) ⋆ ηm (F.F-ob X)
        step10 = sym (C.⋆Assoc (ηu FFT) (G.F-hom ggfx) (ηm (F.F-ob X)))
        
        step11 : ηu FFT ⋆ G.F-hom ggfx ≡ ggfx ⋆ ηu (G.F-ob (F.F-ob X))
        step11 = sym (N-hom nu ggfx)
        
        step12 : (ggfx ⋆ ηu (G.F-ob (F.F-ob X))) ⋆ ηm (F.F-ob X) ≡ ggfx ⋆ (ηu (G.F-ob (F.F-ob X)) ⋆ ηm (F.F-ob X))
        step12 = C.⋆Assoc ggfx (ηu (G.F-ob (F.F-ob X))) (ηm (F.F-ob X))
        
        step13 : ηu (G.F-ob (F.F-ob X)) ⋆ ηm (F.F-ob X) ≡ C.id
        step13 = monad-idˡ
        
        step14 : ggfx ⋆ C.id ≡ ggfx
        step14 = C.⋆IdR ggfx
      in sym step1 ∙ (cong (λ k → k ⋆ ηm (F.F-ob X)) (step2 ∙ (step3 ∙ (step4 ∙ (step5 ∙ (step6 ∙ step7))))) ∙ (step8 ∙ (cong (λ k → k ⋆ (G.F-hom ggfx ⋆ ηm (F.F-ob X))) step9 ∙ (step10 ∙ (cong (λ k → k ⋆ ηm (F.F-ob X)) step11 ∙ (step12 ∙ (cong (λ k → ggfx ⋆ k) step13 ∙ step14)))))))

    from_to-proof : ∀ (τx : NatTrans (CYEF X) (G ∘F F)) (Y : C.ob) → ggfx2τx-η (τx2ggfx τx) Y ≡ N-ob τx Y
    from_to-proof τx Y = 
      let
        A : C.Hom[ FFT , CYEF.F-ob X ]
        A = FF.F-hom (λ _ → C.id)
        B : C.Hom[ CYEF.F-ob X , G.F-ob (F.F-ob X) ]
        B = N-ob τx X
        C_f : C.Hom[ X , Y ] → C.Hom[ G.F-ob (F.F-ob X) , G.F-ob (F.F-ob Y) ]
        C_f = λ f → G.F-hom (F.F-hom f)
        
        step1 : FF.F-hom (λ f → (A ⋆ B) ⋆ C_f f) ⋆ ηm (F.F-ob Y) ≡ 
                FF.F-hom (λ f → A ⋆ (B ⋆ C_f f)) ⋆ ηm (F.F-ob Y)
        step1 = cong (λ k → k ⋆ ηm (F.F-ob Y)) (cong FF.F-hom (funExt (λ f → C.⋆Assoc A B (C_f f))))
        
        step2 : FF.F-hom (λ f → A ⋆ (B ⋆ C_f f)) ≡ FF.F-hom (λ f → A ⋆ (CYEF.F-hom f ⋆ N-ob τx Y))
        step2 = cong FF.F-hom (funExt (λ f → cong (λ k → A ⋆ k) (sym (N-hom τx f))))
        
        step3 : FF.F-hom (λ f → A ⋆ (CYEF.F-hom f ⋆ N-ob τx Y)) ≡ FF.F-hom (λ f → (A ⋆ CYEF.F-hom f) ⋆ N-ob τx Y)
        step3 = cong FF.F-hom (funExt (λ f → sym (C.⋆Assoc A (CYEF.F-hom f) (N-ob τx Y))))
        
        step4 : FF.F-hom (λ f → (A ⋆ CYEF.F-hom f) ⋆ N-ob τx Y) ≡ FF.F-hom (λ f → FF.F-hom (λ _ → C.id ⋆ f) ⋆ N-ob τx Y)
        step4 = cong FF.F-hom (funExt (λ f → cong (λ k → k ⋆ N-ob τx Y) (sym (FF.F-seq (λ _ → C.id) (λ g → g ⋆ f)))))
        
        step5 : FF.F-hom (λ f → FF.F-hom (λ _ → C.id ⋆ f) ⋆ N-ob τx Y) ≡ FF.F-hom (λ f → FF.F-hom (λ _ → f) ⋆ N-ob τx Y)
        step5 = cong FF.F-hom (funExt (λ f → cong (λ k → FF.F-hom {x = T} k ⋆ N-ob τx Y) (funExt (λ _ → C.⋆IdL f))))
        
        step6 : FF.F-hom (λ f → FF.F-hom (λ _ → f) ⋆ N-ob τx Y) ≡ FF.F-hom (λ f → FF.F-hom (λ _ → f)) ⋆ G.F-hom (N-ob τx Y)
        step6 = FF.F-seq (λ f → FF.F-hom (λ _ → f)) (λ k → k ⋆ N-ob τx Y)
        
        step7 : (FF.F-hom (λ f → FF.F-hom (λ _ → f)) ⋆ G.F-hom (N-ob τx Y)) ⋆ ηm (F.F-ob Y) ≡ 
                FF.F-hom (λ f → FF.F-hom (λ _ → f)) ⋆ (G.F-hom (N-ob τx Y) ⋆ ηm (F.F-ob Y))
        step7 = C.⋆Assoc (FF.F-hom (λ f → FF.F-hom (λ _ → f))) (G.F-hom (N-ob τx Y)) (ηm (F.F-ob Y))
        
        step8 : FF.F-hom (λ f → FF.F-hom (λ _ → f)) ≡ ηu (CYEF.F-ob Y)
        step8 = sym (nu-eq {W = CYF X .F-ob Y})
        
        step9 : ηu (CYEF.F-ob Y) ⋆ (G.F-hom (N-ob τx Y) ⋆ ηm (F.F-ob Y)) ≡ (ηu (CYEF.F-ob Y) ⋆ G.F-hom (N-ob τx Y)) ⋆ ηm (F.F-ob Y)
        step9 = sym (C.⋆Assoc (ηu (CYEF.F-ob Y)) (G.F-hom (N-ob τx Y)) (ηm (F.F-ob Y)))
        
        step10 : ηu (CYEF.F-ob Y) ⋆ G.F-hom (N-ob τx Y) ≡ N-ob τx Y ⋆ ηu (G.F-ob (F.F-ob Y))
        step10 = sym (N-hom nu (N-ob τx Y))
        
        step11 : (N-ob τx Y ⋆ ηu (G.F-ob (F.F-ob Y))) ⋆ ηm (F.F-ob Y) ≡ N-ob τx Y ⋆ (ηu (G.F-ob (F.F-ob Y)) ⋆ ηm (F.F-ob Y))
        step11 = C.⋆Assoc (N-ob τx Y) (ηu (G.F-ob (F.F-ob Y))) (ηm (F.F-ob Y))
        
        step12 : ηu (G.F-ob (F.F-ob Y)) ⋆ ηm (F.F-ob Y) ≡ C.id
        step12 = monad-idˡ {X = F.F-ob Y}
        
        step13 : N-ob τx Y ⋆ C.id ≡ N-ob τx Y
        step13 = C.⋆IdR (N-ob τx Y)
      in step1 ∙ (cong (λ k → k ⋆ ηm (F.F-ob Y)) (step2 ∙ (step3 ∙ (step4 ∙ (step5 ∙ step6)))) ∙ (step7 ∙ (cong (λ k → k ⋆ (G.F-hom (N-ob τx Y) ⋆ ηm (F.F-ob Y))) step8 ∙ (step9 ∙ (cong (λ k → k ⋆ ηm (F.F-ob Y)) step10 ∙ (step11 ∙ (cong (λ k → N-ob τx Y ⋆ k) step12 ∙ step13)))))))

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
        {X : SetsObj} (mx : fst (F₀ X)) → 
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

  KleisliFunctionalCategory : Type (lsuc ℓ)
  KleisliFunctionalCategory = FunctionalCategory Kleisli KF

  mPure-mMap-eq :
    ∀ {X : SetsObj} (mx : fst (F₀ X)) → 
      mMap {X} {F₀ X} (mPure {X}) mx ≡ 
        mApply {X} {F₀ X} (λ x → mPure {F₀ X} (mPure {X} x)) mx
  mPure-mMap-eq {X} mx = refl

  idempotent-equiv-kleisli-functional-category : KleisliFunctionalCategory ⇔ Idempotent
  idempotent-equiv-kleisli-functional-category = record
    { to = λ kfc → record 
        { idempotent = λ {X} mx → 
            let
              open FunctionalCategory kfc
              
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
              
              step1 : eval (mApply {X} {F-ob GEFF X} (N-ob nu X) mx) ≡ eval (mPure {F-ob GEFF X} (λ _ → mx))
              step1 = cong eval (sigma-eval-lemma {X} mx)
              
              step2 : eval (mPure {F-ob GEFF X} (λ _ → mx)) ≡ mPure {F₀ X} mx
              step2 = mApply-pure {F-ob GEFF X} {F₀ X} {f = λ g → mPure {F₀ X} (g t)}
              
              step3 : eval (mApply {X} {F-ob GEFF X} (N-ob nu X) mx) ≡ mApply {X} {F₀ X} (λ z → mPure {F₀ X} (mPure {X} z)) mx
              step3 = mApply {F-ob GEFF X} {F₀ X} (λ g → mPure {F₀ X} (g t)) (mApply {X} {F-ob GEFF X} (N-ob nu X) mx)
                  ≡⟨ mApply-assoc {X} {F-ob GEFF X} {F₀ X} ⟩
                mApply {X} {F₀ X} (λ x → mApply {F-ob GEFF X} {F₀ X} (λ g → mPure {F₀ X} (g t)) (N-ob nu X x)) mx
                  ≡⟨ cong (λ k → mApply {X} {F₀ X} k mx) (funExt (λ x → 
                       let
                         inner = sigma-eval-lemma {X} (mPure {X} x)
                         inner-eval = cong eval inner
                         inner-eval2 = mApply-pure {F-ob GEFF X} {F₀ X} {f = λ g → mPure {F₀ X} (g t)}
                         inner-eval3 = cong eval (mApply-pure {X} {F-ob GEFF X} {f = N-ob nu X})
                       in sym inner-eval3 ∙ (inner-eval ∙ inner-eval2)
                     )) ⟩
                mApply {X} {F₀ X} (λ x → mPure {F₀ X} (mPure {X} x)) mx
                  ∎
            in mPure-mMap-eq {X} mx ∙ (sym step3 ∙ (step1 ∙ step2))
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
              
              comm-lhs :
                mApply {GM X} {GM Y} f-lemma (mPure {GM X} (λ _ → mPure {X} x)) ≡ 
                  mPure {GM Y} (λ _ → gmx2mx x)
              comm-lhs = mApply {GM X} {GM Y} f-lemma (mPure {GM X} (λ _ → mPure {X} x))
                  ≡⟨ mApply-pure {GM X} {GM Y} {f = f-lemma} ⟩
                mPure {GM Y} (λ u → mApply {X} {Y} gmx2mx (mPure {X} x))
                  ≡⟨ cong (λ k → mPure {GM Y} (λ _ → k)) (mApply-pure {X} {Y} {f = gmx2mx}) ⟩
                mPure {GM Y} (λ _ → gmx2mx x)
                  ∎
            in sym (comm-lhs ∙ sym (σ-mApply-lemma {Y} (gmx2mx x)))
        in
        record { bfc = record { nu = record 
                  { N-ob = λ X x → mPure {GM X} (λ _ → mPure {X} x)
                  ; N-hom = λ {X Y} f → funExt (λ x → comm {X} {Y} f x)
                  }
               ; nu-eq-T = refl
               }
               ; nu-eq = refl
               ; mu = {!!}
               ; monad-idˡ = {!!}
        }
    }
```
