module lanchonete

--Assinaturas

abstract sig Salgado, Sanduiche, Bebida, Doce{}
sig Coxinha,Empada,Pastel extends Salgado {}
sig SanduicheFrango,SanduicheAtum extends Sanduiche {}
sig Agua,Refrigerante,Suco extends Bebida {}
sig Pudim, Brigadeiro,Torta extends Doce {}

--Pedido tem um conjunto de itens, onde cada item desses pode possuir zero ou mais elementos. (Itens: salgados, sanduiches, doces e bebidas)
abstract sig Pedido{
	salgados : set Salgado,
	sanduiches : set Sanduiche,
	bebidas : set Bebida,
	doces : set Doce
}

--Cliente pode possuir um ou mais pedidos.
sig Cliente {
	pedidos : some Pedido
}

--Lanchonete possui zero ou mais clientes,
one sig Lanchonete {
	clientes : set Cliente
}

--Qualquer pedido que não seja combo,
sig SemCombo extends Pedido{}

--Combo um: tem UM Doce de brinde que pode ser Brigadeiro ou Pudim, é definido mais na frente no predicado TemCombo.
sig ComboUm extends Pedido  {
	brinde : one Doce
}

--Combo dois: tem UMA Torta de brinde, depende do que tem no pedido, é definido no predicado TemCombo,
sig ComboDois extends Pedido  {
	brinde : one Torta
}

--Funções 

--Função que retorna o brinde do ComboUm.
fun getBrindeComboUm[c1: ComboUm] : one Doce {
	c1.brinde
}


--Função que retorna o brinde do ComboDois.
fun getBrindeComboDois[c2: ComboDois] : one Doce {
	c2.brinde
}

--Função que retorna o conjunto de doces de um pedido.
fun getDoces[p:Pedido] : set Doce{
	p.doces
}

--Predicados 

pred show[]{
}

--Todo cliente está ligado a uma lanchonete
pred todoClientePertenceALanchonete{
	all c:Cliente | one c.~clientes
}

--Todo pedido está ligado a um cliente
pred todoPedidoPertenceAUmCliente{
	all p:Pedido |  one p.~pedidos
}

--Todo item está ligado a apenas um pedido
pred todoProdutoPertenceAUmPedido{
	all sa:Salgado |  one sa.~salgados 
	all sd:Sanduiche |  one sd.~sanduiches
	all be:Bebida |  one be.~bebidas
	all do:Doce |  one do.~doces
}

/*Para todo pedido SemCombo:
    O pedido é sem combo se tiver menos de dois salgados e menos de dois sanduiches ou não tiver suco e refrigerante.
    O pedido é sem combo se não tiver refrigerante ou não tiver mais de dois sanduiches e mais de um salgado ou
    se não tiver refrigerante ou não tiver mais de dois salgados e mais de um sanduiche. */
pred naoTemCombo{
	all sc:SemCombo , r: Refrigerante, s: Suco|  !((#(sc.salgados) >= 2 or #(sc.sanduiches) >= 2) and ((r in sc.bebidas) or (s in sc.bebidas))) 
												and 
								       !(r in sc.bebidas and  ((#(sc.salgados) >= 2 and #(sc.sanduiches) >= 1) or (#(sc.sanduiches) >= 2 and #(sc.salgados) >= 1)))   
}

--Para todo ComboUm, o brinde do ComboUm não pode ser torta, sendo assim, pudim ou brigadeiro.
pred comboUmNaoTemTorta {
	all p:ComboUm, t:Torta |  t != getBrindeComboUm[p]
}

--Para todo ComboUm e ComboDois se um doce é brinde, ele não pode estar no conjunto de doces do pedido.
pred brindeNaoEhSobremesa {
	all c:ComboUm | !(getBrindeComboUm[c] in getDoces[c]) 
	all c:ComboDois | !(getBrindeComboDois[c] in getDoces[c]) 
}

/*Para todo ComboUm e ComboDois definimos o que o combo tem que ter para atender as especificações.
    ComboUm tem que ter no minimo dois salgados ou dois sanduiches e deve ter um suco ou um refrigerante
    ComboDois tem que ter no minimo dois salgados e um sanduiche e um refrigerante ou ter no minimo dois sanduiches e um salgado e um refrigerante. */
pred temCombo{
	all p:ComboUm | one r: Refrigerante, s: Suco|  ((#(p.salgados) >= 2 or #(p.sanduiches) >= 2) and ((r in p.bebidas) or (s in p.bebidas)))
	all p:ComboDois | one r:Refrigerante |  r in p.bebidas and  ((#(p.salgados) >= 2 and #(p.sanduiches) >= 1) or (#(p.sanduiches) >= 2 and #(p.salgados) >= 1))
}

--Para todos dois pedidos distintos, p1 e p2, pedidos são diferentes se os itens de um forem diferentes dos itens do outro. (Itens: salgados, sanduiches, doces e bebidas).
--Para todos dois pedidos distintos do tipo ComboUm, c1 e c2, pedidos são diferentes se o brinde de um for diferente do brinde do outro.
--Para todos dois pedidos distintos do tipo ComboDois, c1 e c2, pedidos são diferentes se o brinde de um for diferente do brinde do outro.
--Para todos dois pedidos distintos do tipo ComboUm, c1 e c2, pedidos são diferentes se o brinde de um não estiver nos doces do outro.
--Para todos dois pedidos distintos do tipo ComboDois, c1 e c2, pedidos são diferentes se o brinde de um não estiver nos doces do outro.
--Para todo pedido ComboUm e todo pedido ComboDois, c1 e c2, pedidos são diferentes se o brinde de um não estiver nos doces do outro.
--Para todo pedido ComboUm e todo pedido ComboDois, c1 e c2, pedidos são diferentes se o brinde de um for diferente do brinde do outro.
pred pedidosDiferentes{
	all p1, p2 : Pedido | (p1 != p2) => (p1.bebidas != p2.bebidas and p1.doces != p2.doces and p1.salgados != p2.salgados and p1.sanduiches != p2.sanduiches)
	all c1, c2 : ComboUm | (c1 != c2) => getBrindeComboUm[c1] != getBrindeComboUm[c2]
	all c1, c2 : ComboDois | (c1 != c2) => getBrindeComboDois[c1] != getBrindeComboDois[c2]
	all c1, c2:ComboUm | !(getBrindeComboUm[c1] in getDoces[c2]) 
	all c1, c2:ComboDois | !(getBrindeComboDois[c1] in getDoces[c2])
	all c1:ComboUm , c2:ComboDois |  !(getBrindeComboUm[c1] in getDoces[c2]) 
	all c1:ComboUm , c2:ComboDois |  !(getBrindeComboDois[c2] in getDoces[c1])
	all c1:ComboUm , c2:ComboDois | getBrindeComboUm[c1] != getBrindeComboDois[c2] 
}

--Fatos

--Define todos esses predicados como fatos.
fact {
	todoClientePertenceALanchonete	
	todoPedidoPertenceAUmCliente
	todoProdutoPertenceAUmPedido
	comboUmNaoTemTorta
	brindeNaoEhSobremesa
	naoTemCombo
	temCombo
	pedidosDiferentes
}

--Asserts

assert comboUmTemBrigadeiroOuPudim{
	all p:ComboUm, b:Brigadeiro, pu:Pudim, r: Refrigerante, s: Suco|  (b in p.brinde)  => ((#(p.salgados) >= 2 or #(p.sanduiches) >= 2) and 
	                                                                                                                                ((r in p.bebidas) or (s in p.bebidas)))
	                                                                                               or 
	                                                                                                            (pu in p.brinde)  => ((#(p.salgados) >= 2 or #(p.sanduiches) >= 2) and 
	                                                                                                                                ((r in p.bebidas) or (s in p.bebidas)))	  
}

assert comboDoisTemTortaBrinde{
	all p:ComboDois , t : Torta | some r:Refrigerante | t in p.brinde => ((#(p.salgados) >= 2 and  #(p.sanduiches) >=1)  or  
	                                                        (#(p.sanduiches) >= 2 and #(p.salgados) >= 1)  and r in p.bebidas) 
}

assert ComboDoisNaoTemBrigadeiroBrinde{
	all p : ComboDois, b : Brigadeiro | ! b in getBrindeComboDois[p]
}

check  comboUmTemBrigadeiroOuPudim for 10
check ComboDoisNaoTemBrigadeiroBrinde for 10
check comboDoisTemTortaBrinde for 10


run show for 8 but exactly 4 Cliente, exactly 6 Pedido, exactly 2 ComboDois, exactly 2 ComboUm,  exactly 2 SemCombo
