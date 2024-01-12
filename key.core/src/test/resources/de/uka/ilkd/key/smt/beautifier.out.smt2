(declare-fun f (Int) Int)

; ----------

(assert
  (forall
    ((x Int)
      (x Int)
      (x Int)
      (x Int)
      (x Int)
      (x Int)
      (x Int)
      (x Int)
      (x Int)
      (x Int))
    (> x 0)))

; ----------

(assert
  (forall
    (! ((x Int)) (=> longName________________ (> x 0)) :pattern ((+ 2 x)))))

; ----------

(assert
  |long name with spaces is not broken when longer than 80 characters even this is a ridiculously long name|)

; ----------

(and
  true
  true
  true
  true
  true
  true
  true
  true
  true
  true
  true
  true
  true
  true
  true
  true
  true
  true
  true
  true
  true
  true
  true
  true
  true
  true
  true
  true
  true
  true)

; --------

; Now only comments
; but multiple rows of them!
; with indentations  (which are lost)
; and long lines too xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx xxxxxxxxxxxxxxxx xxxxxxxxxxX

; --------

(assert
  (and
    looooooooooooooooooooooooooooooooooooooooooooong
    short
    ; false false commented out
    after))

; --------

(assert
  (f
    x
    ; inline comments break lines
    (after 42)))

; --------

(assert
  (last is comment)
  ; end of smt problem declaration
  )

; --------
; Problem: New line before ')'
(a b c d)

; --------
; From a bug:
(assert
  (not
    ; The formula to be proved:
    (=> (and (and (= 6 a_2) (= 3 b_3)) (= 2 c_4)) (= c_4 (div a_2 b_3)))))
; End of assert.
(check-sat)
; end of smt problem declaration