#import "../conf.typ": *

== Быстрая сортировка. Поиск порядковой статистики методом "Разделяй и властвуй"

#note("QuickSort")[
  Алгоритм быстрой сортировки:
  - Случайно выбираем опорный элемент (pivot)
  - Всё, что меньше опорного элемента перекинуть влево, а что больше -- вправо
  - Вызвать рекурсивно от правой и левой половины.
  Минусы:
  - Использует доппамять, так как нужно хранить стек рекурсии
  - Под любую стратегию выбора опорного элемента можно построить контрданные так, чтобы работало квадратичное время с линейной доппамятью.
]

#theorem[
  Среднее время работы быстрой сортировки составляет $O(N log N)$, если опорный элемент выбирается равновероятно.
]

#definition[
  *k-й порядковой статистикой* массива называют элемент, который после сортировки будет стоять на $k$-м месте.
]

#note("QuickSelect")[
  Алгоритм быстрого поиска:
  - Выбрать опорный элемент
  - Провести разбиение
  - Если индекс опорного элемента окажется больше, чем $k$ -- то ищем слева $k$-ю статистику, иначе, справа -- $k - i - 1$-ю.
]

#theorem[
  Среднее время работы алгоритма выше составляет $O(N)$, если опорный элемент выбирается равновероятно.
]
