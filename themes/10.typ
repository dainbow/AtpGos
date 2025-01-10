#import "../conf.typ": *

== Двоичное дерево поиска. Обходы в глубину и в ширину. Поиск ключа, наивные вставка и удаление ключа. АВЛ-дерево.

#definition[
  *Деревом поиска* называют дерево, в котором в поддереве левее все элементы не больше элемента в данном узле, а в поддереве правее -- строго больше.

  Пусть $h$ -- высота дерева, тогда мы хотим
  #eq[
    #table(
      align: (center, center),
      columns: 2,
      [*Операция*], [*Время*],
      [Вставка элемента], [$O(h)$],
      [Поиск элемента], [$O(h)$],
      [Удаление элемента], [$O(h)$],
    )
  ]
  Поиск в таком дереве тривиальный -- начинаем с корня, если искомый ключ меньше -- идём влево, иначе -- вправо. Если элемент есть -- мы его найдём, иначе -- попытаемся зайти в несуществующий узел.

  Для вставки мы пойдём аналогично поиску, но когда дойдём до несуществующего узла -- то добавим его на это место.

  Иллюстрация удаления:
  #image("../assets/treeRemove.png")
]

#definition[
  Дерево поиска является *AVL-деревом*, если для каждой вершины высота её правого и левого поддеревьев различаются не более, чем на единицу.
]

#theorem[
  Высота AVL-дерева равна $O(log N)$.
]

#definition[
  *Балансировкой* AVL-дерева будем называть процесс, который из дерева поиска, в узле которого разных высот подедревьев равна двум, переподвешивает детей и внуков так, чтобы выполнялось свойство AVL-дерева.

  #image("../assets/treeBalance.png")

  Симметрично определяются два правых поворота.

  После каждой операции изменения дерева, запускаем балансировку от нового узла до корня, причём баланс уже сбалансированных поддеревьев никак не изменится.
]