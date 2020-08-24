
(: foo type)
(define foo type)
(: bar foo)
(define bar foo)

(: baz unit)
(define baz trivial)

(: test (exists (x type) x))
(define test (tuple type type))

(: id (forall (A type) (x A) A))
(define id (lambda (A x) x))

(: const (forall (A type) (B type) (x A) (y B) A))
(define const (lambda (A B x y) y))
