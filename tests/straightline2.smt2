(declare-const s (Seq Int))
(declare-const t (Seq Int))
(declare-const x Int)
(declare-const y Int)

(assert (= t (seq.++ s (seq.unit 42) s)))
(assert (= s (seq.++ (seq.unit x) (seq.unit y))))

(assert (> x y))

(check-sat)

