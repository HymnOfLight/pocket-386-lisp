;;; ============================================================
;;; WL.LSP   -   Weisfeiler-Lehman graph isomorphism test
;;;             (1-WL color refinement   +   2-FWL "folklore")
;;;             with CFI-style counterexample graphs and
;;;             ASCII visualisation, for Apteryx Lisp on Pocket 386.
;;;
;;; The whole file is ~ 500 lines / ~ 14 KB and uses only:
;;;   defun cond if and or let setq defvar princ terpri
;;;   cons car cdr cadr null atom consp list equal eq
;;;   + - * = < > <= >= zerop
;;; That subset is in every Lisp 1.5 derivative, including
;;; Apteryx Lisp 1.04.
;;; ============================================================


;;; ============================================================
;;; 0.  TINY UTILITIES
;;; ============================================================

(defun mem-int (x lst)
  (cond ((null lst) nil)
        ((= x (car lst)) t)
        (t (mem-int x (cdr lst)))))

(defun length-of (lst)
  (cond ((null lst) 0)
        (t (+ 1 (length-of (cdr lst))))))

(defun range-aux (i n)
  (cond ((>= i n) nil)
        (t (cons i (range-aux (+ i 1) n)))))

(defun rng (n) (range-aux 0 n))

(defun insert-int-sorted (x lst)             ; sorted, *no* dedup
  (cond ((null lst) (list x))
        ((< x (car lst)) (cons x lst))
        (t (cons (car lst) (insert-int-sorted x (cdr lst))))))

(defun insert-int-set (x lst)                 ; sorted, dedup
  (cond ((null lst) (list x))
        ((< x (car lst)) (cons x lst))
        ((= x (car lst)) lst)
        (t (cons (car lst) (insert-int-set x (cdr lst))))))

(defun sort-int-multiset (lst)
  (cond ((null lst) nil)
        (t (insert-int-sorted (car lst) (sort-int-multiset (cdr lst))))))

(defun assoc-equal (k a)
  (cond ((null a) nil)
        ((equal k (car (car a))) (car a))
        (t (assoc-equal k (cdr a)))))

(defun int-assoc (k a)                         ; faster: integer key
  (cond ((null a) nil)
        ((= k (car (car a))) (car a))
        (t (int-assoc k (cdr a)))))

(defun cdrs (a)
  (cond ((null a) nil)
        (t (cons (cdr (car a)) (cdrs (cdr a))))))

;;; Convert a sorted multiset of integers into the sorted list of
;;; class sizes (the "partition signature").  Two graphs are
;;; distinguished by a colouring iff their partition signatures differ.
(defun ms-to-sizes (ms)
  (cond ((null ms) nil)
        (t (let ((p (split-run (car ms) ms 0)))
             (cons (car p) (ms-to-sizes (cdr p)))))))
(defun split-run (x lst k)
  (cond ((null lst) (cons k nil))
        ((= (car lst) x) (split-run x (cdr lst) (+ k 1)))
        (t (cons k lst))))

(defun insert-desc (x lst)
  (cond ((null lst) (list x))
        ((> x (car lst)) (cons x lst))
        (t (cons (car lst) (insert-desc x (cdr lst))))))
(defun sort-desc (lst)
  (cond ((null lst) nil)
        (t (insert-desc (car lst) (sort-desc (cdr lst))))))

(defun partition-sig (c)
  (sort-desc (ms-to-sizes (sort-int-multiset (cdrs c)))))


;;; ============================================================
;;; 1.  GRAPH REPRESENTATION
;;;       g  ::=  (cons N adj)
;;;       adj  ::=  ((0 . nbrs0) (1 . nbrs1) ... (N-1 . nbrsN-1))
;;;       nbrs_i is a sorted, dedup-ed list of neighbour indices
;;; ============================================================

(defun gn   (g) (car g))
(defun gadj (g) (cdr g))

(defun init-adj (n)
  (init-adj-aux 0 n))
(defun init-adj-aux (i n)
  (cond ((>= i n) nil)
        (t (cons (cons i nil) (init-adj-aux (+ i 1) n)))))

(defun alist-add (key val a)
  (cond ((null a) nil)
        ((= (car (car a)) key)
           (cons (cons key (insert-int-set val (cdr (car a)))) (cdr a)))
        (t (cons (car a) (alist-add key val (cdr a))))))

(defun add-edge (e a)
  (let ((u (car e)) (v (cadr e)))
    (alist-add v u (alist-add u v a))))

(defun fold-edges (a edges)
  (cond ((null edges) a)
        (t (fold-edges (add-edge (car edges) a) (cdr edges)))))

(defun mk-graph (n edges)
  (cons n (fold-edges (init-adj n) edges)))

(defun gnbrs (g v) (cdr (int-assoc v (gadj g))))

(defun adjacent? (g u v) (mem-int v (gnbrs g u)))


;;; ============================================================
;;; 2.  COLOUR CANONICALISER
;;;       maps an arbitrary key (a list) to a fresh small integer.
;;;       Reset before each refinement step so that the integers
;;;       used by two graphs being compared are commensurable.
;;; ============================================================

(defvar *colmap* nil)
(defvar *colnext* 0)

(defun cm-reset ()
  (setq *colmap*  nil)
  (setq *colnext* 0))

(defun cm-get (key)
  (let ((p (assoc-equal key *colmap*)))
    (cond (p (cdr p))
          (t (let ((id *colnext*))
               (setq *colmap*  (cons (cons key id) *colmap*))
               (setq *colnext* (+ id 1))
               id)))))


;;; ============================================================
;;; 3.  1-WL  (color refinement)
;;; ============================================================

(defun init-coloring (g)
  (init-col-aux 0 (gn g)))
(defun init-col-aux (i n)
  (cond ((>= i n) nil)
        (t (cons (cons i 0) (init-col-aux (+ i 1) n)))))

(defun col-of (v c) (cdr (int-assoc v c)))

(defun map-cols (vs c)
  (cond ((null vs) nil)
        (t (cons (col-of (car vs) c) (map-cols (cdr vs) c)))))

(defun nbr-color-ms (g v c)
  (sort-int-multiset (map-cols (gnbrs g v) c)))

(defun wl1-step (g c)
  (wl1-step-aux 0 (gn g) g c))
(defun wl1-step-aux (i n g c)
  (cond ((>= i n) nil)
        (t (cons (cons i (cm-get (cons (col-of i c) (nbr-color-ms g i c))))
                 (wl1-step-aux (+ i 1) n g c)))))

(defun colorings= (a b)
  (cond ((null a) (null b))
        ((null b) nil)
        ((= (cdr (car a)) (cdr (car b))) (colorings= (cdr a) (cdr b)))
        (t nil)))

(defun color-multiset (c) (sort-int-multiset (cdrs c)))

;;; Run two graphs jointly: each refinement step uses one fresh
;;; canonicaliser shared by both, so equal locally-isomorphic
;;; neighbourhoods get equal integer colours across the pair.
;;; Returns  (final-c1  final-c2  history-c1  history-c2  iters).
(defun wl1-refine-pair (g1 g2 max-iter)
  (let ((c1 (init-coloring g1))
        (c2 (init-coloring g2)))
    (wl1-loop g1 g2 c1 c2 0 max-iter (list c1) (list c2))))

(defun wl1-loop (g1 g2 c1 c2 i max h1 h2)
  (cond
    ((>= i max) (list c1 c2 (rev h1) (rev h2) i))
    (t
       (cm-reset)
       (let ((c1n (wl1-step g1 c1)))
         (let ((c2n (wl1-step g2 c2)))
           (cond
             ((and (colorings= c1n c1) (colorings= c2n c2))
                (list c1 c2 (rev h1) (rev h2) i))
             (t (wl1-loop g1 g2 c1n c2n (+ i 1) max
                          (cons c1n h1) (cons c2n h2)))))))))

(defun rev (l)
  (rev-aux l nil))
(defun rev-aux (l acc)
  (cond ((null l) acc)
        (t (rev-aux (cdr l) (cons (car l) acc)))))

(defun wl1-distinguishes? (c1 c2)
  (not (equal (color-multiset c1) (color-multiset c2))))


;;; ============================================================
;;; 4.  2-FWL  (folklore 2-Weisfeiler-Lehman)
;;;       colours pairs (i,j); inductive step uses a "witness"
;;;       vertex k:   c'(i,j) = HASH(c(i,j), {(c(i,k),c(k,j)) : k}).
;;;       2-FWL has the same expressive power as the (3-)WL
;;;       described in Cai-Furer-Immerman.
;;; ============================================================

(defun atomic-type (g i j)
  (cond ((= i j) 'diag)
        ((adjacent? g i j) 'edge)
        (t 'non-edge)))

(defun init-2coloring (g)
  (init-2c-aux 0 0 (gn g) g))
(defun init-2c-aux (i j n g)
  (cond ((>= i n) nil)
        ((>= j n) (init-2c-aux (+ i 1) 0 n g))
        (t (cons (cons (list i j) (cm-get (atomic-type g i j)))
                 (init-2c-aux i (+ j 1) n g)))))

(defun pair-col (i j c) (cdr (assoc-equal (list i j) c)))

(defun pair< (a b)
  (cond ((< (car a) (car b)) t)
        ((= (car a) (car b)) (< (cadr a) (cadr b)))
        (t nil)))

(defun insert-pair (p lst)
  (cond ((null lst) (list p))
        ((pair< p (car lst)) (cons p lst))
        (t (cons (car lst) (insert-pair p (cdr lst))))))

(defun sort-pair-list (lst)
  (cond ((null lst) nil)
        (t (insert-pair (car lst) (sort-pair-list (cdr lst))))))

(defun witnesses (i j n c)
  (sort-pair-list (witnesses-aux i j 0 n c)))
(defun witnesses-aux (i j k n c)
  (cond ((>= k n) nil)
        (t (cons (list (pair-col i k c) (pair-col k j c))
                 (witnesses-aux i j (+ k 1) n c)))))

(defun wl2-step (g c)
  (let ((n (gn g))) (wl2-step-aux 0 0 n g c)))
(defun wl2-step-aux (i j n g c)
  (cond ((>= i n) nil)
        ((>= j n) (wl2-step-aux (+ i 1) 0 n g c))
        (t (cons (cons (list i j)
                       (cm-get (cons (pair-col i j c) (witnesses i j n c))))
                 (wl2-step-aux i (+ j 1) n g c)))))

(defun col2= (a b)
  (cond ((null a) (null b))
        ((null b) nil)
        ((= (cdr (car a)) (cdr (car b))) (col2= (cdr a) (cdr b)))
        (t nil)))

(defun wl2-refine-pair (g1 g2 max-iter)
  (cm-reset)
  (let ((c1 (init-2coloring g1)))
    (let ((c2 (init-2coloring g2)))
      (wl2-loop g1 g2 c1 c2 0 max-iter))))

(defun wl2-loop (g1 g2 c1 c2 i max)
  (cond ((>= i max) (list c1 c2 i))
        (t
           (cm-reset)
           (let ((c1n (wl2-step g1 c1)))
             (let ((c2n (wl2-step g2 c2)))
               (cond ((and (col2= c1n c1) (col2= c2n c2))
                        (list c1 c2 i))
                     (t (wl2-loop g1 g2 c1n c2n (+ i 1) max))))))))

(defun wl2-distinguishes? (c1 c2)
  (not (equal (color-multiset c1) (color-multiset c2))))


;;; ============================================================
;;; 5.  ASCII VISUALISATION
;;; ============================================================

(defun pad2 (n)                                  ; print n right-padded
  (cond ((< n 10) (princ " ") (princ n))
        (t       (princ n))))

(defun show-adj (g)
  (princ "  adjacency matrix:") (terpri)
  (princ "      ")
  (show-adj-header 0 (gn g)) (terpri)
  (show-adj-rows 0 (gn g) g))
(defun show-adj-header (i n)
  (cond ((>= i n) nil)
        (t (princ " ") (pad2 i) (show-adj-header (+ i 1) n))))
(defun show-adj-rows (i n g)
  (cond ((>= i n) nil)
        (t (princ "    ") (pad2 i) (princ ":")
           (show-adj-row 0 n i g) (terpri)
           (show-adj-rows (+ i 1) n g))))
(defun show-adj-row (j n i g)
  (cond ((>= j n) nil)
        (t (princ "  ")
           (cond ((adjacent? g i j) (princ "*"))
                 (t                 (princ ".")))
           (show-adj-row (+ j 1) n i g))))

(defun show-coloring-row (label c)
  (princ label) (princ " : ")
  (show-cv c))
(defun show-cv (c)
  (cond ((null c) (terpri))
        (t (pad2 (cdr (car c))) (princ " ") (show-cv (cdr c)))))

(defun show-history (label hist)
  (princ "  ") (princ label) (princ " - 1-WL colour history") (terpri)
  (princ "    iter |")
  (show-history-header 0 (length-of (car hist))) (terpri)
  (princ "    -----+")
  (show-dashes (* 3 (length-of (car hist)))) (terpri)
  (show-history-rows 0 hist))
(defun show-history-header (i n)
  (cond ((>= i n) nil)
        (t (princ " ") (pad2 i) (show-history-header (+ i 1) n))))
(defun show-dashes (k)
  (cond ((<= k 0) nil)
        (t (princ "-") (show-dashes (- k 1)))))
(defun show-history-rows (i hist)
  (cond ((null hist) nil)
        (t (princ "      ") (pad2 i) (princ " |")
           (show-cv-h (car hist))
           (show-history-rows (+ i 1) (cdr hist)))))
(defun show-cv-h (c)
  (cond ((null c) (terpri))
        (t (princ " ") (pad2 (cdr (car c))) (show-cv-h (cdr c)))))


;;; ============================================================
;;; 6.  SAMPLE GRAPHS
;;; ============================================================

;; --- demo A : K_{1,3}  vs  P_4   (1-WL distinguishes immediately) ---
(defun g-claw () (mk-graph 4 '((0 1) (0 2) (0 3))))
(defun g-p4   () (mk-graph 4 '((0 1) (1 2) (2 3))))

;; --- demo B : 2K_3  vs  C_6     (both 2-regular -> 1-WL fails) ---
(defun g-2k3  () (mk-graph 6 '((0 1) (1 2) (2 0)
                               (3 4) (4 5) (5 3))))
(defun g-c6   () (mk-graph 6 '((0 1) (1 2) (2 3) (3 4) (4 5) (5 0))))

;; --- demo C : K_{3,3}  vs  triangular prism (3-prism)
;;     both 3-regular on 6 vertices -> 1-WL fails;
;;     2-FWL distinguishes: prism has triangles, K_{3,3} has none.
(defun g-k33   () (mk-graph 6 '((0 3) (0 4) (0 5)
                                (1 3) (1 4) (1 5)
                                (2 3) (2 4) (2 5))))
(defun g-prism () (mk-graph 6 '((0 1) (1 2) (2 0)            ; top triangle
                                (3 4) (4 5) (5 3)            ; bot triangle
                                (0 3) (1 4) (2 5))))         ; rungs

;; --- demo D : a CFI-style pair, base graph C_3 (triangle)
;;     CFI gadget for a degree-2 vertex v with incident edges {e,f}:
;;       inner vertices  : a_emptyset(v), a_{e,f}(v)            (2)
;;       endpoint vtxs   : p_e_v_0, p_e_v_1, p_f_v_0, p_f_v_1   (4)
;;       internal edges  : a_emptyset -- p_e_v_0,  a_emptyset -- p_f_v_0,
;;                         a_{e,f}    -- p_e_v_1,  a_{e,f}    -- p_f_v_1
;;
;;     For each base edge {u,v}: connect  p_e_u_b -- p_e_v_b  (untwisted)
;;                            or          p_e_u_0 -- p_e_v_1
;;                                         p_e_u_1 -- p_e_v_0  (twisted)
;;
;;     Vertex numbering for C_3 (3 gadgets G0 G1 G2, edges 01, 12, 02):
;;        Gv has vertices  6v + {0:a_emptyset, 1:a_{e,f},
;;                              2:p_e_v_0, 3:p_e_v_1,
;;                              4:p_f_v_0, 5:p_f_v_1}
;;     where for v=0 e=01 f=02; for v=1 e=01 f=12; for v=2 e=12 f=02.
;;
;;     We build CFI(C_3) twice: untwisted and edge-01-twisted.

(defun cfi-internal (v)                    ; 4 internal edges of gadget v
  (let ((b  (* 6 v)))
    (list (list (+ b 0) (+ b 2))           ; a_emptyset -- p_e_v_0
          (list (+ b 0) (+ b 4))           ; a_emptyset -- p_f_v_0
          (list (+ b 1) (+ b 3))           ; a_{e,f}    -- p_e_v_1
          (list (+ b 1) (+ b 5)))))        ; a_{e,f}    -- p_f_v_1

;; For each base edge (u,v) we must say which endpoint slot in gadget
;; u and gadget v belongs to that base edge.  In our numbering
;;   v=0 :  slot e (offset 2/3) = base-edge 01 ;  slot f (4/5) = base-edge 02
;;   v=1 :  slot e              = 01           ;  slot f      = 12
;;   v=2 :  slot e              = 12           ;  slot f      = 02
;; A small lookup:
(defun slot-of (v ed)                       ; returns 'e or 'f
  (cond ((and (= v 0) (equal ed '(0 1))) 'e)
        ((and (= v 0) (equal ed '(0 2))) 'f)
        ((and (= v 1) (equal ed '(0 1))) 'e)
        ((and (= v 1) (equal ed '(1 2))) 'f)
        ((and (= v 2) (equal ed '(1 2))) 'e)
        ((and (= v 2) (equal ed '(0 2))) 'f)))
(defun slot-base (slot)
  (cond ((eq slot 'e) 2) (t 4)))            ; offset of the slot's "0"-vtx

(defun cfi-edge-pair (ed twist?)
  ;; returns the two cross-gadget edges for base edge ed
  (let ((u  (car ed)) (v (cadr ed)))
    (let ((bu (slot-base (slot-of u ed))) (bv (slot-base (slot-of v ed))))
      (let ((u0 (+ (* 6 u) bu)) (u1 (+ (* 6 u) bu 1))
            (v0 (+ (* 6 v) bv)) (v1 (+ (* 6 v) bv 1)))
        (cond (twist? (list (list u0 v1) (list u1 v0)))
              (t      (list (list u0 v0) (list u1 v1))))))))

(defun cfi-c3 (twisted-edge)
  ;; twisted-edge = nil   (untwisted CFI(C_3))
  ;; twisted-edge = '(0 1) (twist base edge 0-1)
  (let ((e1 '(0 1)) (e2 '(1 2)) (e3 '(0 2)))
    (let ((internal
            (append (cfi-internal 0)
                    (append (cfi-internal 1) (cfi-internal 2))))
          (cross
            (append (cfi-edge-pair e1 (equal twisted-edge e1))
                    (append (cfi-edge-pair e2 (equal twisted-edge e2))
                            (cfi-edge-pair e3 (equal twisted-edge e3))))))
      (mk-graph 18 (append internal cross)))))

(defun g-cfi-untw () (cfi-c3 nil))
(defun g-cfi-tw   () (cfi-c3 '(0 1)))


;;; ============================================================
;;; 7.  DEMO DRIVER
;;; ============================================================

(defun banner (s)
  (terpri) (princ "============================================") (terpri)
  (princ s) (terpri)
  (princ "============================================") (terpri))

(defun report-pair (lab1 g1 lab2 g2)
  (terpri) (princ "[ Graphs ]") (terpri)
  (princ "  ") (princ lab1) (princ ":") (terpri) (show-adj g1)
  (princ "  ") (princ lab2) (princ ":") (terpri) (show-adj g2))

(defun show-sig (c)
  (princ "[")
  (show-sig-list (partition-sig c))
  (princ "]"))
(defun show-sig-list (l)
  (cond ((null l) nil)
        ((null (cdr l)) (princ (car l)))
        (t (princ (car l)) (princ " ") (show-sig-list (cdr l)))))

(defun report-1wl (lab1 lab2 res)
  (let ((c1 (car res))   (c2 (car (cdr res)))
        (h1 (car (cdr (cdr res))))
        (h2 (car (cdr (cdr (cdr res)))))
        (it (car (cdr (cdr (cdr (cdr res)))))))
    (princ "[ 1-WL ]  stable after ") (princ it)
    (princ " refinement step(s)") (terpri)
    (show-history lab1 h1)
    (show-history lab2 h2)
    (princ "  ") (princ lab1) (princ " partition  ") (show-sig c1) (terpri)
    (princ "  ") (princ lab2) (princ " partition  ") (show-sig c2) (terpri)
    (princ "  >>> 1-WL distinguishes ? ")
    (cond ((wl1-distinguishes? c1 c2) (princ "YES")) (t (princ "NO")))
    (terpri)))

(defun report-2wl (lab1 lab2 res)
  (let ((c1 (car res)) (c2 (car (cdr res))) (it (car (cdr (cdr res)))))
    (princ "[ 2-FWL ] stable after ") (princ it)
    (princ " refinement step(s)") (terpri)
    (princ "  ") (princ lab1) (princ " 2-partition  ") (show-sig c1) (terpri)
    (princ "  ") (princ lab2) (princ " 2-partition  ") (show-sig c2) (terpri)
    (princ "  >>> 2-FWL distinguishes ? ")
    (cond ((wl2-distinguishes? c1 c2) (princ "YES")) (t (princ "NO")))
    (terpri)))

(defun do-demo (title lab1 g1 lab2 g2 run2?)
  (banner title)
  (report-pair lab1 g1 lab2 g2)
  (report-1wl  lab1 lab2 (wl1-refine-pair g1 g2 30))
  (cond (run2? (report-2wl lab1 lab2 (wl2-refine-pair g1 g2 15)))
        (t (princ "[ 2-FWL ] (skipped on Pocket 386 - too slow for this size)")
           (terpri))))

(defun demo ()
  (terpri)
  (princ "Weisfeiler-Lehman test on Pocket 386 / Apteryx Lisp")
  (terpri)
  (princ "===================================================")
  (terpri)

  (do-demo "DEMO A : K_{1,3}  vs  P_4   (1-WL works via degrees)"
           "K13 " (g-claw) " P4 " (g-p4) t)

  (do-demo "DEMO B : 2K_3  vs  C_6   (both 2-regular -> 1-WL FAILS)"
           "2K3 " (g-2k3) " C6 " (g-c6) t)

  (do-demo "DEMO C : K_{3,3}  vs  3-prism   (both 3-reg -> 1-WL FAILS)"
           "K33 " (g-k33) "Pr3 " (g-prism) t)

  (do-demo "DEMO D : CFI(C_3) untwisted vs twisted (CFI counterexample)"
           "Untw" (g-cfi-untw) "Twst" (g-cfi-tw) t)

  (terpri) (princ "done.") (terpri))

(demo)
