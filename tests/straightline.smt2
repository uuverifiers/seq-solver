(declare-const s (Seq Int))
(declare-const t (Seq Int))

(assert (= t (seq.++ s (seq.unit 42) s)))
(assert (= s (seq.++ (seq.unit 1) (seq.unit 2))))

(check-sat)

