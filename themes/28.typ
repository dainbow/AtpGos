#import "../conf.typ": *

== Иерархическая и сетевая модели данных

#note("Иерархическая модель данных")[
  Основные свойства:
  - В основе -- структура дерева.
  - Предполагается работать с файлами, содержащими тройки значений $angles("сущность, свойство, значение")$.
  - Хранение такой модели в виде таблиц не эффективно, так как таблицы получаются разряженными.
  - Из-за деревьев имеют структуру: один потомок -- множество предков.
]

#example("Иерархической модели")[
  #image("../assets/IMG.png")
]

#note("Сетева модель данных")[
  Основные свойства:
  - В основе -- запись.
  - Запись имеет именованные поля
  - Часть полей отводится под ссылки на другие записи
  - Записи формируют цепи
  - Первая запись в цепи -- мастер-запись
  - Каждая последующая запись имеет прямую ссылку на мастер-запись, последовательность записей замкнута на мастер-запись
  - Цепь записей представляет собой отношение
  - Допустима и множественность потомков, и множественность предков
]

#example("Сетевой модели")[
  #image("../assets/netData.png")
]
