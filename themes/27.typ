#import "../conf.typ": *

== Теорема Майхилла-Нероуда. Лемма о разрастании. Пример неавтоматных языков.

#theorem("Майхилла-Нероуда")[
  $L$ -- автоматный $<=>$ $L$ содержит конечное количество классов эквивалентности $Sigma^*_(\/ tilde_L)$
]

#proof[
  $L$ - автоматный $=> abs(Sigma^*_(\/ tilde_L) <= abs(Q) < +oo)$

  Для языка с конечным количеством классов эквивалентности построим канонический МПДКА.
]

#lemma("О разрастании для автоматных языков")[
  Пусть $L$ -- автоматный язык. Тогда
  #eq[
    $exists P in NN : forall w in L : abs(w) >= P : \
      exists x,y,z : w = x y z : abs(x y) <= P, abs(y) != 0 : forall k in NN : x y^k z in L$
  ]
]

#proof[
  Построим НКА с 1-буквенными переходами, распознающий данный язык.

  Тогда $P := abs(Q)$. Если $abs(w) >= P => $ посетили $P + 1$ состояние.

  Значит $exists q in Q$, которую посетили дважды, значит мы можем ходить по этому циклу любое $k$ число раз.
]

#example("Неавтоматный язык")[
  #eq[
    $L = {a^n b^n | n in NN}$
  ]
]

#proof[
  Докажем неавтоматность отрицанием леммы о разрастании:
  #eq[
    $forall P in NN : exists w in L : abs(w) >= P : \
      forall x,y,z : w = x y z : abs(x y) <= P, abs(y) != 0 : exists k in NN : x y^k z in.not L$
  ]
  Для любого $P$ возьмём $w = a^P b^P in L$. Тогда любой префикс $abs(x y) <= P$ будет содержать только $a$, но тогда при разрастании любого $y$ количество $a$ будет увеличиваться, а $b$ -- нет.

  Такое слово никак не сможет лежать в исходном языке. Доказали.
]