#import "../conf.typ": *

== Нахождение подстроки в строке

#definition[
  Строка $T$ называется *супрефиксом* строки $S$, если она является одновременно и префиксом, и суффиксом строки $S$.
]

#definition[
  *Префикс-функцией* от строки $S$ называют такой массив $pi(S)$ длины $abs(S)$, что $pi(S)[i]$ равно длине максимального несобственного супрефикса строки $S[:i]$.
]

#note("Линейный алгоритм построения")[
  Заметим, что $pi[i + 1] <= pi[i] + 1$. Это верно, так как, добавив 1 символ к максимальному суффиксу, мы увеличим длину максимального супрефикса не более, чем на 1.

  Теперь осознаем, что
  #eq[
    $pi[i + 1] = max_(s, s "супрефикс" S[:i], S[abs(s)] = S[i + 1]) (abs(s) + 1)$
  ]
  то есть мы пытаемся "расширить" подходящий супрефикс подстроки $S[:i]$, а "расширить" его можно, только если после его префикса идёт символ, равный $S[i + 1]$.

  Осталось осознать, что все супрефиксы имеют длины $pi[i], pi[pi[i]], ...$. Рассмотрим $S[:i]$:
  #eq[
    $cases(S[:pi[i]] = S[i - pi[i]:i], S[:pi[pi[i]]] = S[pi[i] - pi[pi[i]]:pi[i]]) => S[:pi[pi[i]]] = S[i - pi[pi[i]]:i]$
  ]
  Итого, получаем, что $pi[i + 1] = pi[j] + 1$, где $j$ -- первый подходящий индекс из последовательности $i, pi[i], pi[pi[i]], ...$, такой, что $S[pi[j]] = S[i + 1]$.
]

#note("Алгоритм Кнута-Морриса-Пратта")[
  Дана цепочка $T$ и образец $P$. Требуется найти все позиции, начиная с которых $P$ входит в $T$.

  Построим цепочку $S = P hash T$, где $hash$ -- любой символ не входящий в алфавит искомых строк.

  Вычислим от этой строки префикс-функцию $pi$, тогда, если в какой-то момент $pi[i] = abs(P)$, значит мы нашли конец вхождения $P$ в $T$, то есть допишем в ответ $i - abs(P)$.
]