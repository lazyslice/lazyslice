
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

(: const (forall (A type) (B type) (x A) (y B) B))
(define const (lambda (A B x y) y))

(: test2 (forall (x type) type))
(define test2 (id type))

(: test3 (const type type type unit))
(define test3 baz)

(: Bool type)
(data Bool
    (: false Bool)
    (: true Bool))

(: test4 Bool)
(define test4 true)

(: Maybe (forall (A type) type))
(data Maybe
    (: nothing (forall (A type) (Maybe A)))
    (: just (forall (A type) (x A) (Maybe A))))

(: test5 (Maybe Bool))
(define test5 (just Bool true))
