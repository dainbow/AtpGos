#import "../conf.typ": *

== Детерминированные конечные автоматы. Эквивалентность ДКА и НКА.

#definition[
  НКА $M = angles(Q\, Sigma\, Delta\, q_0\, F)$ называется *детерминированным* (ДКА), если
  - $forall (angles(q_1\, w) -> q_2) in Delta' : abs(w) = 1$
  - $forall a in Sigma, q in Q : abs(Delta(q, a)) <= 1$
]

#theorem[
  Для любого НКА $M = angles(Q\, Sigma\, Delta\, q_0\, F)$ существует ДКА $M'$, такой, что $L(M) = L(M')$.
]

#proof[
  Обозначим $Delta(S, w) = union_(q in S) Delta(q, w)$, где $w in Sigma^*, S subset Q$.

  Построим ДКА $M' = angles(2^Q\, Sigma\, Delta\, {q_0}\, F')$, где
  - $F' = {S subset Q | S sect F != emptyset}$
  - $Delta' = {angles(S\, a) -> Delta(S\, a), a in Sigma}$ -- состояния, куда ведут рёбра по $a$ из элементов $S$
  - $2^Q$ -- множество всех подмножеств старых состояний
]

#lemma[
  Для доказательства эквивалентности покажем, что
  #eq[
    $forall w in Sigma^*: Delta'({q_0}, w) = Delta({q_0}, w)$
  ]
  , где слева -- вершина $M'$, а справа -- подмножество вершин в $M$.
]

#proof[
  Докажем индукцией по длине слова $w$

  База:
  #eq[
    $w = epsilon => Delta({q_0}, epsilon) = {q_0} = Delta'({q_0}, epsilon)$
  ]
  Переход:
  Пусть $w = u a, u in Sigma^*, a in Sigma$, сначала покажем, что $Delta({q_0}, u a) = Delta(Delta({q_0}, u), a)$:
  #eq[
    $Delta({q_0}, u a) = {q | angles(q_0\, u a) tack angles(q\, epsilon)} = {q | exists q' : angles(q_0\, u a) tack angles(q'\, a) tack angles(q\, epsilon)} = \
      {q | exists q' in Delta({q_0}, u): angles(q'\, a) tack angles(q\, epsilon)} = Delta(Delta({q_0}, u), a)$
  ]

  Но мы знаем, что $Delta({q_0}, u) = Delta'({q_0}, u)$ по предположению индукции, а $Delta(S, a) = Delta'(S, a)$ по определению $Delta'$.
]
