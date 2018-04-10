#lang racket/base

(require
  redex/reduction-semantics)
(module+ test
  (require rackunit))

(provide (all-defined-out))

(define-language ecc
  (i j k   ::= natural)
  (U       ::= (Type i))
  (e A B   ::= x U (λ (x : A) e) (e e) (Π (x : A) B) (Σ (x : A) B) (pair e e (Σ (x : A) B)) (fst e) (snd e))
  (x       ::= variable-not-otherwise-mentioned)
  (Γ       ::= ∅ (Γ x : A))
  (v       ::= x (Type i) (λ (x : v) v) (Π (x : v) v) n (pair v v v) (Σ (x : v) v))
  (n       ::= x (fst n) (snd n) (n v))

  #:binding-forms
  (λ (x : A) e #:refers-to x)
  (Π (x : A) e #:refers-to x)
  (Σ (x : A) e #:refers-to x))

(define-metafunction ecc
  Γ-ref : Γ x -> A or #f
  [(Γ-ref ∅ x) #f]
  [(Γ-ref (Γ x : A) x) A]
  [(Γ-ref (Γ x_0 : A_0) x) (Γ-ref Γ x)])

(define ecc-->
  (reduction-relation ecc
    (--> ((λ (x : A) e_0) e_1) (substitute e_0 x e_1))
    (--> (fst (pair e_1 e_2 A)) e_1)
    (--> (snd (pair e_1 e_2 A)) e_2)))

(define ecc-->* (compatible-closure ecc--> ecc e))

(define-metafunction ecc
  [(reduce e) ,(car (apply-reduction-relation* ecc-->* (term e)))])

(module+ test
  (require racket/function)
  (check (curry alpha-equivalent? ecc)
    (term (reduce ((λ (x : (Type 0)) x) z)))
    (term z)))

(define-judgment-form ecc
  #:mode (convert I I)
  #:contract (convert e e)

  [(where (e_2 e_2) ((reduce e_0) (reduce e_1)))
   --------------
   (convert e_0 e_1)])

(define-judgment-form ecc
  #:mode (valid I)
  #:contract (valid Γ)

  [--------------------
   (valid ∅)]

  [(type-infer Γ A U)
   (valid Γ)
   --------------------
   (valid (Γ x : A))])

(define-judgment-form ecc
  #:mode (type-infer I I O)
  #:contract (type-infer Γ e A)

  [(where A (Γ-ref Γ x))
   (valid Γ)
   -----------------------
   (type-infer Γ x A)]

  [(valid Γ)
   (where j ,(add1 (term i)))
   -------------------------------
   (type-infer Γ (Type i) (Type j))]

  [(type-infer (Γ x : A) e B)
   -------------------------------------------
   (type-infer Γ (λ (x : A) e) (Π (x : A) B))]

  [(type-infer Γ A (Type j))
   (type-infer (Γ x : A) B (Type k))
   (where i ,(max (term j) (term k)))
   -------------------------------------
   (type-infer Γ (Π (x : A) B) (Type i))]

  [(type-check (Γ x : A) B (Type 0))
   -------------------------------------
   (type-infer Γ (Π (x : A) B) (Type 0))]

  [(type-infer Γ e_0 (Π (x : A) B))
   (type-check Γ e_1 A)
   --------------------------
   (type-infer Γ (e_0 e_1) (substitute B x e_1))]

  [(type-infer Γ e_1 A)
   (type-check Γ e_2 (substitute B x e_1))
   --------------------------
   (type-infer Γ (pair e_1 e_2 (Σ (x : A) B)) (Σ (x : A) B))]

  [(type-infer Γ e (Σ (x : A) B))
   --------------------------
   (type-infer Γ (fst e) A)]

  [(type-infer Γ e (Σ (x : A) B))
   --------------------------
   (type-infer Γ (snd e) (substitute B x (fst e)))]

  [(type-infer Γ A (Type j))
   (type-infer (Γ x : B) B (Type k))
   (where i ,(max (term j) (term k)))
   --------------------------
   (type-infer Γ (Σ (x : A) B) (Type i))])


(define-judgment-form ecc
  #:mode (type-check I I I)
  #:contract (type-check Γ e A)

  [(type-infer Γ e A)
   (type-infer Γ B U)
   (convert A B)
   -----------------
   (type-check Γ e B)])


;; tests

(define-metafunction ecc
  Γ-build : Γ (x : A) ... -> Γ
  [(Γ-build Γ) Γ]
  [(Γ-build Γ (x_r : A_r) ...  (x : A))
   ((Γ-build Γ (x_r : A_r) ...) x : A)])

(define-metafunction ecc
  Γ-flatten : Γ -> ((x : A) ...)
  [(Γ-flatten ∅) ()]
  [(Γ-flatten (Γ x : A))
   ((x_r : A_r) ... (x : A))
   (where ((x_r : A_r) ...) (Γ-flatten Γ))])

(module+ test
  (define-syntax-rule (check-holds (id args ...))
    (check-true
      (judgment-holds (id args ...))))
  (define-syntax-rule (check-not-holds (id args ...))
    (check-false
      (judgment-holds (id args ...))))
  (check-holds
    (type-infer ∅ (Type 0) (Type 1)))
  (check-holds
    (type-check ∅ (Type 0) (Type 1)))
  (check-not-holds
    (type-check ∅ (Π (x : (Type 0)) (Type 0)) (Type 0)))
  (check-holds
    (type-check ∅ (Π (x : (Type 0)) (Type 0)) (Type 1)))
  (check-not-holds
    (type-check ∅ (Π (x : (Type 0)) x) (Type 0)))

  (check-holds
    (type-infer ∅ (λ (A : (Type 0)) (λ (x : A) x)) (Π (A : (Type 0)) (Π (x : A) A))))

  (define-term Γp
    (Γ-build
      (Nat : (Type 0))
      (z : Nat)
      (s : (Π (x : Nat) Nat))))

  (check-holds
    (type-check Γp z Nat))

  (check-holds
    (type-check Γp (s (s z)) Nat))

  (check-holds
   (type-check Γp (λ (x : Nat) x) (Π (x : Nat) Nat)))

  (check-equal?
   (term (Γ-flatten Γp))
   (term ((Nat : (Type 0))
    (z : Nat)
          (s : (Π (x : Nat) Nat)))))

  (define-term Γ=
    (Γ-build Γp
      (= : (Π (A : (Type 0)) (Π (a : A) Π (b : A) (Type 1))))
      (refl : (Π (A : (Type 0)) (Π (a : A) (((= A) a) a))))))

  (check-holds (valid Γ=))
  (check-holds (type-infer Γ= (((= Nat) z) z) (Type 1)))
  (check-holds (type-infer Γ= ((refl Nat) z) (((= Nat) z) z)))
  (check-holds (type-infer (pair z ((refl Nat) z) (Σ (x : Nat) ((= Nat) x z)))))

#;(redex-check ecc #:satisfying (type-check ∅ e A) (redex-match? ecc v (term (reduce e))) #:attempt 10))
