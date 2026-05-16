;;; ============================================================
;;; LCF.LSP   -   A minimal LCF-style proof kernel
;;; ------------------------------------------------------------
;;; Target machine : Pocket 386 (ALi M6117 / 386SX, 8 MB DRAM).
;;; Target dialect : Apteryx Lisp 1.04 (Win 3.x).
;;;
;;; The whole point of LCF style is: there is exactly ONE place in
;;; the system where values of type THM are constructed - the kernel.
;;; Every theorem reachable in the running image was therefore built
;;; by a finite chain of kernel-rule applications. Soundness of the
;;; entire proof system reduces to inspecting just the few small
;;; functions in the section labelled  "PRIMITIVE INFERENCE RULES".
;;;
;;; Object logic:
;;;   classical propositional logic with implication and falsity.
;;;   Terms (formulas) are:
;;;     a propositional variable - any non-special symbol
;;;     BOT                      - falsum
;;;     (IMP a b)                - implication a -> b
;;;   Negation is defined as  ~A  =def=  (IMP A BOT)
;;;
;;; Sequents are pairs  (Hyps, Conclusion) where Hyps is a finite
;;; SET of formulas (we use lists modulo EQUAL, no duplicates).
;;;
;;; ============================================================


;;; ============================================================
;;; 0.  TINY UTILITIES (avoid sequence library for portability)
;;; ============================================================

(defun mem-eq (x s)
  (cond ((null s) nil)
        ((equal x (car s)) t)
        (t (mem-eq x (cdr s)))))

(defun add-h (x s)
  (cond ((mem-eq x s) s)
        (t (cons x s))))

(defun union-h (a b)
  (cond ((null a) b)
        (t (union-h (cdr a) (add-h (car a) b)))))

(defun remove-h (x s)
  (cond ((null s) nil)
        ((equal x (car s)) (remove-h x (cdr s)))
        (t (cons (car s) (remove-h x (cdr s))))))

;;; ============================================================
;;; 1.  TERMS  (concrete - nothing private here)
;;; ============================================================

(defun mk-imp (a b) (list 'imp a b))
(defun mk-not (a)   (list 'imp a 'bot))

(defun is-imp (tm)
  (and (consp tm) (eq (car tm) 'imp)))
(defun imp-ant (tm) (car (cdr tm)))
(defun imp-cnq (tm) (car (cdr (cdr tm))))

(defun term= (a b) (equal a b))


;;; ============================================================
;;; 2.  THE THM ABSTRACT DATA TYPE
;;; ------------------------------------------------------------
;;; Apteryx Lisp does not have an ML-style module system, so we
;;; cannot mechanically hide a constructor.  We approximate the
;;; abstraction with a "private" tag: every theorem is internally
;;; (TAG  Hyps  Concl)
;;; and TAG is bound to a freshly consed cell created at load time.
;;; Client code is documented to never inspect the cdr of *KTAG*
;;; nor call MK-THM directly; the published interface consists ONLY
;;; of the inference rules and the read-only accessors HYPS/CONCL.
;;;
;;; The "by-convention" abstraction is exactly what Milner's original
;;; LCF/Edinburgh-LCF papers note as the role of ML's signature
;;; declarations: discipline + a small kernel = trustworthy theorems.
;;; ============================================================

;; DEFVAR keeps the same cell across reloads (so theorems already
;; built in the listener stay valid).  If your Lisp lacks DEFVAR,
;; replace this with  (setq *ktag* (cons 'lcf-private-tag nil)).
(defvar *ktag* (cons 'lcf-private-tag nil))   ; fresh, unforgeable cons

(defun mk-thm (hyps concl)
  (cons *ktag* (cons hyps (cons concl nil))))

(defun is-thm (x)
  (and (consp x) (eq (car x) *ktag*)))

(defun hyps  (th) (car (cdr th)))
(defun concl (th) (car (cdr (cdr th))))

;;; A halting error reporter for unsound rule applications.  If
;;; Apteryx Lisp's built-in ERROR has a different name, edit here.
(defun kfail (msg)
  (princ "*** KERNEL ERROR: ") (princ msg) (terpri)
  (error msg))


;;; ============================================================
;;; 3.  PRIMITIVE INFERENCE RULES  (the *only* trusted code)
;;; ------------------------------------------------------------
;;; If every one of the five functions below takes inputs that
;;; represent valid sequents and produces an output representing a
;;; valid sequent of classical propositional logic with -> and BOT,
;;; then the whole system is sound.  No other code in this file is
;;; in the trusted base.
;;; ============================================================

;;; (1)  ASSUME : -------------
;;;               { A } |- A
(defun rule-assume (a)
  (mk-thm (list a) a))

;;; (2)  MODUS PONENS :
;;;       G |- A->B      D |- A
;;;       ----------------------
;;;            G u D |- B
(defun rule-mp (th1 th2)
  (cond
    ((not (is-thm th1)) (kfail "MP: 1st arg not a thm"))
    ((not (is-thm th2)) (kfail "MP: 2nd arg not a thm"))
    ((not (is-imp (concl th1)))
       (kfail "MP: 1st conclusion is not an implication"))
    ((not (term= (imp-ant (concl th1)) (concl th2)))
       (kfail "MP: antecedent does not match"))
    (t (mk-thm (union-h (hyps th1) (hyps th2))
               (imp-cnq (concl th1))))))

;;; (3)  DEDUCTION (DISCH) :
;;;          G |- B
;;;       ----------------
;;;       G \ {A} |- A->B
(defun rule-disch (a th)
  (cond ((not (is-thm th)) (kfail "DISCH: not a thm"))
        (t (mk-thm (remove-h a (hyps th))
                   (mk-imp a (concl th))))))

;;; (4)  EX-FALSO (intuitionistic explosion) :
;;;       G |- BOT
;;;       --------
;;;        G |- A
(defun rule-ex-falso (a th)
  (cond ((not (is-thm th)) (kfail "EX-FALSO: not a thm"))
        ((not (term= (concl th) 'bot))
           (kfail "EX-FALSO: conclusion is not BOT"))
        (t (mk-thm (hyps th) a))))

;;; (5)  PEIRCE's law as a classical seed axiom :
;;;       ------------------------------
;;;        |- ((A->B) -> A) -> A
(defun rule-peirce (a b)
  (mk-thm nil (mk-imp (mk-imp (mk-imp a b) a) a)))

;;; --------- end of trusted kernel (5 functions, ~30 lines) ---------


;;; ============================================================
;;; 4.  DERIVED RULES  (untrusted; built only via kernel calls)
;;; ------------------------------------------------------------
;;; Every value returned by these functions is a chain of kernel
;;; calls, so each is automatically as sound as the kernel itself.
;;; The kernel never grows; only this section grows.
;;; ============================================================

;;; refl :  |- A -> A
(defun derived-refl (a)
  (rule-disch a (rule-assume a)))

;;; axiom-K (derivable in natural deduction) :  |- A -> B -> A
(defun derived-k (a b)
  (rule-disch a
    (rule-disch b
      (rule-assume a))))

;;; axiom-S (derivable) :  |- (A -> B -> C) -> (A -> B) -> A -> C
(defun derived-s (a b c)
  (let ((h-abc (mk-imp a (mk-imp b c)))
        (h-ab  (mk-imp a b)))
    (rule-disch h-abc
      (rule-disch h-ab
        (rule-disch a
          (rule-mp
            (rule-mp (rule-assume h-abc) (rule-assume a))   ; B->C
            (rule-mp (rule-assume h-ab)  (rule-assume a))))))))   ; B

;;; trans :  G |- A->B   D |- B->C    ===>   G u D |- A->C
(defun derived-trans (th1 th2)
  (let ((a (imp-ant (concl th1))))
    (rule-disch a
      (rule-mp th2 (rule-mp th1 (rule-assume a))))))

;;; not-elim (modus tollens with negation):
;;;   G |- ~A     D |- A      ===>     G u D |- BOT
;;; (recall ~A == A -> BOT)
(defun derived-not-elim (th-na th-a)
  (rule-mp th-na th-a))

;;; double-negation elimination (classical):  |- ~~A -> A
(defun derived-dne (a)
  (let ((nna (mk-not (mk-not a)))
        (na  (mk-not a)))
    ;; under hyp nna and hyp na we derive BOT, then EX-FALSO -> A
    (let ((bot-th (rule-mp (rule-assume nna) (rule-assume na))))
      (let ((a-th  (rule-ex-falso a bot-th)))
        ;; discharge na, giving (under nna) :  na -> A
        (let ((nna-na->a (rule-disch na a-th)))
          ;; combine with Peirce ((na -> A) -> A) to get A under nna
          (let ((a-under-nna
                  (rule-mp (rule-peirce a 'bot) nna-na->a)))
            (rule-disch nna a-under-nna)))))))

;;; contraposition (intuitionistic):
;;;   |- (A -> B) -> (~B -> ~A)
(defun derived-contra (a b)
  (let ((h-ab (mk-imp a b))
        (h-nb (mk-not b)))
    (rule-disch h-ab
      (rule-disch h-nb
        (rule-disch a
          (rule-mp (rule-assume h-nb)
                   (rule-mp (rule-assume h-ab)
                            (rule-assume a))))))))


;;; ============================================================
;;; 5.  PRETTY PRINTING
;;; ============================================================

(defun show-term (tm)
  (cond ((atom tm) (princ tm))
        ((is-imp tm)
           (princ "(")
           (show-term (imp-ant tm))
           (princ " -> ")
           (show-term (imp-cnq tm))
           (princ ")"))
        (t (princ tm))))

(defun show-hyps (h)
  (cond ((null h) nil)
        ((null (cdr h)) (show-term (car h)))
        (t (show-term (car h)) (princ ", ") (show-hyps (cdr h)))))

(defun show-thm (th)
  (cond
    ((not (is-thm th))
       (princ "<<not a theorem!>>"))
    (t
       (cond ((null (hyps th)) (princ "       |- "))
             (t (show-hyps (hyps th)) (princ " |- ")))
       (show-term (concl th)))))

(defun report-thm (label th)
  (princ label)
  (princ "  ")
  (show-thm th)
  (terpri))


;;; ============================================================
;;; 6.  DEMO PROOFS
;;; ============================================================

(defun demo ()
  (terpri)
  (princ "Minimal LCF Kernel - demo on Pocket 386 / Apteryx Lisp")
  (terpri)
  (princ "------------------------------------------------------")
  (terpri) (terpri)

  (princ "[A] Primitive rules") (terpri)
  (report-thm "  ASSUME p             :" (rule-assume 'p))
  (report-thm "  PEIRCE p,q           :" (rule-peirce 'p 'q))
  (report-thm "  DISCH p of (p|-p)    :"
          (rule-disch 'p (rule-assume 'p)))
  (report-thm "  MP of K p q and (p)  :"
          (rule-mp (derived-k 'p 'q) (rule-assume 'p)))
  (terpri)

  (princ "[B] Derived rules (provably sound by construction)") (terpri)
  (report-thm "  refl p               :" (derived-refl 'p))
  (report-thm "  axiom-K p q          :" (derived-k 'p 'q))
  (report-thm "  axiom-S p q r        :" (derived-s 'p 'q 'r))
  (report-thm "  trans (p->q)(q->r)   :"
          (derived-trans
            (rule-assume (mk-imp 'p 'q))
            (rule-assume (mk-imp 'q 'r))))
  (report-thm "  contra p q           :" (derived-contra 'p 'q))
  (report-thm "  ~~p -> p   (DNE)     :" (derived-dne 'p))
  (terpri)

  (princ "[C] A small worked theorem:  |- (p -> q) -> (~~p -> q)")
  (terpri)
  ;; Proof:
  ;;   1. h1 : p -> q          (assume)
  ;;   2. h2 : ~~p             (assume)
  ;;   3.       ~~p -> p       (DNE)
  ;;   4.       p              (MP 3, 2)
  ;;   5.       q              (MP 1, 4)
  ;;   6.       ~~p -> q       (disch h2)
  ;;   7. |- (p->q) -> (~~p->q)  (disch h1)
  (let ((h1 (mk-imp 'p 'q)))
    (let ((step1 (rule-assume h1))
          (step2 (rule-assume (mk-not (mk-not 'p))))
          (dne   (derived-dne 'p)))
      (let ((p-th (rule-mp dne step2)))
        (let ((q-th (rule-mp step1 p-th)))
          (let ((nnp->q (rule-disch (mk-not (mk-not 'p)) q-th)))
            (let ((final (rule-disch h1 nnp->q)))
              (report-thm "  result :" final)))))))
  (terpri)

  (princ "[D] Abstraction sanity check") (terpri)
  ;; A fake "theorem" - syntactically a list, but built without
  ;; calling any kernel rule.  IS-THM must reject it.
  (let ((forged (list (cons 'lcf-private-tag nil) nil 'bot)))
    (princ "  Forged value passes IS-THM ? ")
    (princ (is-thm forged)) (terpri)
    (princ "  (must be NIL: the tag is a fresh cons, not the symbol)")
    (terpri))
  ;; A genuine theorem must be accepted.
  (princ "  Real theorem passes IS-THM ? ")
  (princ (is-thm (derived-refl 'p))) (terpri)

  (terpri)
  (princ "done.") (terpri))

(demo)
