;;; ============================================================
;;; DPLL.LSP   -   DPLL SAT solver for Apteryx Lisp on Pocket 386
;;; ------------------------------------------------------------
;;; Target machine : Pocket 386 (ALi M6117 @ 40 MHz, 386SX core,
;;;                  no FPU, 8 MB RAM, Win 3.11 / DOS).
;;; Target dialect : Apteryx Lisp 1.04 (Win 3.x).
;;;
;;; Coding style is kept minimal on purpose:
;;;   - Only basic specials (DEFUN, IF, COND, AND, OR, LET, QUOTE).
;;;   - Only basic primitives (CAR CDR CONS NULL EQ EQUAL ATOM
;;;                            =, <, >, +, -, ABS, PRINC, TERPRI).
;;;   - No LOOP, no FORMAT directives, no keyword args, no &OPTIONAL,
;;;     no LET*, no DESTRUCTURING-BIND, no CLOS, no sequence library.
;;;   - Recursive helpers only: every list is walked with CAR / CDR
;;;     so the interpreter does not have to allocate auxiliary
;;;     vectors or hash tables (precious on 8 MB).
;;;   - Integer literals are used to encode propositional literals
;;;     (positive int = positive literal, negative int = negation).
;;;     This avoids consing (NOT x) wrappers and keeps clauses very
;;;     short - important on the 386SX where heap traffic is slow.
;;; ============================================================

;;; ------------------------------------------------------------
;;; Encoding
;;;   variable           : positive integer 1..N
;;;   literal            : nonzero integer  (sign = polarity)
;;;   clause             : list of literals (disjunction)
;;;   CNF formula        : list of clauses  (conjunction)
;;;   model / assignment : list of literals known to be TRUE
;;; ------------------------------------------------------------

(defun neg (lit) (- 0 lit))

;;; -- list helpers (kept tiny so we do not depend on REMOVE etc.) ---

(defun mem-int (x lst)
  (cond ((null lst)         nil)
        ((= x (car lst))    t)
        (t                  (mem-int x (cdr lst)))))

(defun del-int (x lst)
  (cond ((null lst)         nil)
        ((= x (car lst))    (del-int x (cdr lst)))
        (t                  (cons (car lst) (del-int x (cdr lst))))))

;;; -- CNF transforms ------------------------------------------------

;;; SIMPLIFY:  given that LIT is true, return a new clause-list with
;;;   - every clause that already contains LIT removed
;;;   - (NEG LIT) deleted from every remaining clause
(defun simplify (clauses lit)
  (cond
    ((null clauses) nil)
    ((mem-int lit (car clauses))
       (simplify (cdr clauses) lit))
    (t (cons (del-int (neg lit) (car clauses))
             (simplify (cdr clauses) lit)))))

;;; FIND-UNIT:  return the literal of the first unit clause, or NIL.
(defun find-unit (clauses)
  (cond
    ((null clauses) nil)
    ((and (car clauses)                 ; clause non-empty
          (null (cdr (car clauses))))   ; and has exactly one literal
       (car (car clauses)))
    (t (find-unit (cdr clauses)))))

;;; HAS-EMPTY?: true if any clause is the empty list (a contradiction).
(defun has-empty (clauses)
  (cond
    ((null clauses) nil)
    ((null (car clauses)) t)
    (t (has-empty (cdr clauses)))))

;;; PICK-LIT:  branching heuristic.  We just take the first literal of
;;;   the first clause - the cheapest possible choice and good enough
;;;   for the small puzzles we run on the Pocket 386.
(defun pick-lit (clauses) (car (car clauses)))

;;; -- DPLL core -----------------------------------------------------
;;;
;;; Returns either the satisfying model (a list of literals)
;;; or the symbol UNSAT.
;;;
;;; Pure-literal elimination is intentionally skipped: scanning the
;;; whole formula for polarities is expensive, and unit propagation
;;; alone solves the toy benchmarks below quickly enough.
;;;
(defun dpll (clauses model)
  (cond
    ((null clauses)      model)              ; no clauses left -> SAT
    ((has-empty clauses) 'unsat)             ; empty clause    -> UNSAT
    (t
      (let ((u (find-unit clauses)))
        (cond
          (u (dpll (simplify clauses u) (cons u model)))
          (t
            (let ((l (pick-lit clauses)))
              (let ((try (dpll (simplify clauses l) (cons l model))))
                (cond
                  ((not (eq try 'unsat)) try)        ; positive branch
                  (t (dpll (simplify clauses (neg l)) ; negative branch
                           (cons (neg l) model))))))))))))

;;; ------------------------------------------------------------
;;; Pretty printing
;;; ------------------------------------------------------------

(defun show-lit (l)
  (cond ((< l 0) (princ "-") (princ (abs l)))
        (t      (princ l))))

(defun show-clause (c)
  (princ "(")
  (show-clause-1 c)
  (princ ")"))

(defun show-clause-1 (c)
  (cond ((null c) nil)
        ((null (cdr c)) (show-lit (car c)))
        (t (show-lit (car c)) (princ " ") (show-clause-1 (cdr c)))))

(defun show-cnf (cs)
  (cond ((null cs) nil)
        (t (show-clause (car cs))
           (cond ((cdr cs) (princ " ^ ")))
           (show-cnf (cdr cs)))))

(defun show-model (m)
  (cond ((null m) nil)
        (t (show-lit (car m))
           (cond ((cdr m) (princ " ")))
           (show-model (cdr m)))))

;;; ------------------------------------------------------------
;;; Driver / banner
;;; ------------------------------------------------------------

(defun solve (name clauses)
  (princ "---- ") (princ name) (princ " ----") (terpri)
  (princ " CNF : ") (show-cnf clauses)        (terpri)
  (let ((r (dpll clauses nil)))
    (cond
      ((eq r 'unsat)
         (princ " RES : UNSAT") (terpri))
      (t (princ " RES : SAT  { ") (show-model r) (princ " }") (terpri))))
  (terpri))

;;; ------------------------------------------------------------
;;; A handful of small propositions
;;;
;;; Encoding key (per problem):
;;;   P1: 1=A 2=B
;;;   P2: 1=A
;;;   P3: 1=A 2=B 3=C
;;;   P4: 1=P 2=Q 3=R
;;;   P5: 1=x11 2=x12 3=x21 4=x22 5=x31 6=x32
;;;       (3 pigeons in 2 holes  ->  UNSAT)
;;;   P6: 1=x11 2=x12 3=x13 4=x21 5=x22 6=x23 7=x31 8=x32 9=x33
;;;       (3 pigeons in 3 holes  ->  SAT, an injective assignment)
;;; ------------------------------------------------------------

(defun run-tests ()
  (terpri)
  (princ "DPLL on Pocket 386 / Apteryx Lisp") (terpri)
  (princ "=================================") (terpri) (terpri)

  ;; P1:  (A v B) ^ (~A v B)               -- expect SAT, B = T
  (solve "P1  (A v B) and (~A v B)"
         '((1 2) (-1 2)))

  ;; P2:  A ^ ~A                           -- expect UNSAT
  (solve "P2  A and ~A"
         '((1) (-1)))

  ;; P3:  (A v B) ^ (~A v C) ^ (~B v ~C)   -- expect SAT
  (solve "P3  (A v B) ^ (~A v C) ^ (~B v ~C)"
         '((1 2) (-1 3) (-2 -3)))

  ;; P4:  modus-ponens style:
  ;;   (P -> Q) ^ (Q -> R) ^ P ^ ~R         -- expect UNSAT
  ;;   = (~P v Q) ^ (~Q v R) ^ (P) ^ (~R)
  (solve "P4  (P->Q) ^ (Q->R) ^ P ^ ~R"
         '((-1 2) (-2 3) (1) (-3)))

  ;; P5:  pigeonhole 3-into-2  -- expect UNSAT
  (solve "P5  pigeonhole 3-in-2 (UNSAT)"
         '(( 1  2)        ; pigeon 1 in some hole
           ( 3  4)        ; pigeon 2 in some hole
           ( 5  6)        ; pigeon 3 in some hole
           (-1 -3)        ; not both p1,p2 in hole 1
           (-1 -5)
           (-3 -5)
           (-2 -4)        ; not both p1,p2 in hole 2
           (-2 -6)
           (-4 -6)))

  ;; P6:  pigeonhole 3-into-3  -- expect SAT
  (solve "P6  pigeonhole 3-in-3 (SAT)"
         '(( 1  2  3)     ; pigeon 1 in some hole
           ( 4  5  6)     ; pigeon 2 in some hole
           ( 7  8  9)     ; pigeon 3 in some hole
           (-1 -4) (-1 -7) (-4 -7)   ; hole 1 unique
           (-2 -5) (-2 -8) (-5 -8)   ; hole 2 unique
           (-3 -6) (-3 -9) (-6 -9))) ; hole 3 unique

  (princ "done.") (terpri))

;;; In Apteryx Lisp the file is LOADed and then evaluated; uncomment
;;; the next form, or simply type  (run-tests)  at the listener.
(run-tests)
