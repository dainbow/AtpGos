#import "../conf.typ": *

== Декартово дерево. Декартово дерево по неявному ключу.

#definition[
  *Декартовым деревом* называют бинарное дерево, содержащее в себе пары $(x_i, y_i)$, при этом данное дерево является деревом поиска по *ключам* и бинарной пирамидой по *приоритетам*.

  У декартова дерева есть две фундаментальные операции: split и merge.
]

#note("Split")[
  Операция Split принимает на вход декартово дерево $T$ и ключ $k$, а возвращает пару декартовых деревьев $T_1, T_2$ таких, что в $T_1$ все ключи не больше $k$, а в $T_2$ все ключи строго больше.

  Пусть ключ в корне окажется меньше, чем ключ, по которому разрезаем, тогда:
  - Левое поддерево $T_1$ совпадает с левым поддеревом $T$. Для нахождения правого поддерева $T_1$ рекурсивно по тому же ключу разрежем правого сына $T$ на $T_L, T_R$. Тогда правым поддеревом $T_1$ будет $T_L$.
  - $T_2$ совпадает с $T_R$.
  Выполняется данная операция, очевидно, за $O(h)$.
]

#note("Merge")[
  Данная операция принимает на вход два декартовых дерева $(T_1, T_2)$ таких, что все ключи в $T_1$ меньше ключей в $T_2$. Рассмотрим два случая:
  - Приоритет корня левого поддерева больше приоритета корня правого. Тогда верно, что левое поддерево итогового дерева $T$ совпадает с левым поддеревом $T_1$, а правой будет результатом слияния правого поддерева $T_1$ и $T_2$.
  - Приоритет корня левого поддерева меньше приоритета корня правого. Тогда верно, что правое поддерево итогового дерева $T$ совпадет с правым поддеревом $T_2$, а левое будет результатом слияния $T_1$ и левого поддерева $T$.
  Данная операция также выполняется за $O(h)$.
]

#note("Вставка и удаление")[
  Обсудим вставку элемента с ключом $k$:
  - $"Split"(T, k) =: (T_1, T_2)$
  - Смотрим, совпадает ли наибольший элемент в $T_1$ с $k$. Если да, то мёрджим $T_1, T_2$, иначе идём дальше
  - Создаём $T_3$ дерево-синглетон над вставляемым элементом и делаем $"Merge"("Merge"(T_1, T_3), T_2)$
]

#theorem("Глубина декартова дерева")[
  В декартовом дереве из $N$ узлов, приоритеты у которого являются случайными величинами с равномерным распределением, средняя глубина вершины $O(log n)$.
]

#note("Декартово дерево по неявному ключу")[
  Хотим получить "быстрый" динамический массив:
  #eq[
    #table(
      columns: 2,
      align: (center, center),
      [*Операция*], [*Время*],
      [Отрезание конца массива], [$O(log n)$],
      [Конкатенация массивов], [$O(log n)$],
      [Получение по индексу], [$O(log n)$],
      [Удаление по индексу], [$O(log n)$],
      [Вставка по индексу], [$O(log n)$],
      [Перестановка подотрезка], [$O(log n)$],
    )
  ]
  Для этого будем использовать декартово дерево, но ключом будет не индекс элемента в массиве, а число элементов в его поддеревьях, что позволит нам за константу пересчитывать эту характеристику при удалениях или вставках.
]