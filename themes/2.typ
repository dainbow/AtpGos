#import "../conf.typ": *

== Связные списки. Стек, очередь, дека и их реализации

#note("Список")[
  Мы хотим от списка следующее:
  #eq[
    #table(
      columns: 2,
      align: (center, center),
      [*Операция*], [*Время*],
      [Вставка в известное место], [O(1)],
      [Удаление из известного места], [O(1)],
      [Поиск], [O(N)],
      [Обращение по индексу], [O(N)],
    )
  ]
  Наш список будет хранить цепочку из узлов, где каждый указывает на следующего за ним, а последний указывает в никуда.

  Поиск и обращение по индексу требуют линейного прохода, но при этом вставка или удаление элемента -- это создание узла и переприсвоение указателей.

  Существует также двусвязный список -- хранит в себе два указателя на узел после и позади нас. Благодаря дополнительному указателю, получаем возможность работы с обоими концами списка, не теряя в асимптотике.
]

#note("Стек")[
  Мы хотим от стека следующее:
  #eq[
    #table(
      columns: 2,
      align: (center, center),
      [*Операция*], [*Время*],
      [Вставка в начало], [O(1)],
      [Удаление из начала], [O(1)],
      [Узнать размер], [O(1)],
    )
  ]
  Стек можно реализовать на односвязном списке, однако для быстрого получения размера следует завести счётчик, изменяемый при вставке/удалении.
]

#note("Очередь")[
  Мы хотим от очереди следующее:
  #eq[
    #table(
      columns: 2,
      align: (center, center),
      [*Операция*], [*Время*],
      [Вставка в начало], [O(1)],
      [Удаление из конца], [O(1)],
      [Узнать размер], [O(1)],
    )
  ]
  Очередь тривиально реализуется на двухсвязном списке, однако есть способ реализовать её на двух стеках.

  У нас будут два стека: входной и выходной. Вставка будет происходить в перывй, а удаление из второго. В случае удаление из пустого выходного стека требуется переложить все элементы из выходного стека в выходной (получим развёрнутый выходной стек).

  Удаление из такой очереди уже будет $O^* (1)$, так как на каждый элемент хватит по 3 монетки -- на его добавление, переброс в выходной стек и удаление.
]

#note("Дека")[
  Деку иногда называют двусторонним стеком или двусторонней очередью:
  #eq[
    #table(
      columns: 2,
      align: (center, center),
      [*Операция*], [*Время*],
      [Вставка в начало или в конец], [O(1)],
      [Удаление из начала или из конца], [O(1)],
      [Узнать размер], [O(1)],
    )
  ]
  Тривиально реализуется на двухсвязном списке.
]