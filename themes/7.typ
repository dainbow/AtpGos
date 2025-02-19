#import "../conf.typ": *

== Динамическое программирование: общая идея, линейная динамика, матричная, динамика на отрезках

#definition[
  *Динамическое программирование* -- способ решения алгоритмических задач, который основывается на переходе от частного к общему.
]

#note("Нахождение наибольшей возрастающей подпоследовательности")[
  Построим массив $d$, где $d[i]$ -- это длина наибольшей возрастающей подпоследовательности, оканчивающейся в элементе с индексом $i$.

  Пусть искомая последовательность -- $a$.

  Массив будет заполняться следующим образом:
  #eq[
    $d[i] = cases(1\, i = 0, 1 + max_(j = 0 ... i - 1; a[j] < a[i]) d[j])$
  ]
  Причём в случае максимума по пустому множеству будет возвращаться 0.

  Данная задачка является примером линейного ДП с квадратичной сложностью.
]

#note("Нахождение наибольшей общей подпоследовательности")[
  Построим матрицу $d$, где $d[i, j]$ -- это длина наибольшей общей подпоследовательности, оканчивающаяся в первой последовательности на $i$-м индексе, а во второй -- на $j$-м.

  Пусть искомые последовательность -- $s_1, s_2$.

  Тогда заполним матрицу:
  #eq[
    $d[n_1, n_2] = cases(0\, n_1 = 0 or n_2 = 0, d[n_1 - 1, n_2 - 1] + 1\, s_1[n_1 - 1] = s_2[n_2 - 1], max(d[n_1 - 1, n_2], d[n_1, n_2 - 1])\, "else")$
  ]

  Данная задачка является примером матричного ДП с квадратичной сложностью.
]

#note("ДП на подотрезках")[
  В рассмотренных задачах у нас была "индукция" по индексам массива или матрицы, однако часто можно встретить "индукцию" по длинам подотрезков.

  Например, пусть есть строка $S$ и надо найти длину максимальной подпоследовательности палиндрома.

  Пусть $f(l, r)$ -- ответ для подстроки $S[l : r + 1]$, тогда сразу определим базу $f(l, l) = 1$ и $f(l, r) = 0, r < l$.

  Сразу опредилимся, что ответом будет $f(0, abs(S) - 1)$.

  Теперь научимся пересчитывать ответ. У нас могут быть две ситуации:
  - Если $S[l] = S[r]$, то нам выгодно добавить эти символы к итоговому палиндрому, а значит $f(l, r) = f(l + 1, r - 1) + 2$.
  - Если же $S[l] != S[r]$, то просто прокинем максимум из подстрок $f(l, r) = max(f(l + 1, r), f(l, r - 1))$.
]
