module lanchonete

--Assinaturas

abstract sig Salgado, Sanduiche, Bebida, Doce{}
sig Coxinha,Empada,Pastel extends Salgado {}
sig SanduicheFrango,SanduicheAtum extends Sanduiche {}
sig Agua,Refrigerante,Suco extends Bebida {}
sig Pudim, Brigadeiro,Torta extends Doce {}

abstract sig Pedido{
	salgados : set Salgado,
	sanduiches : set Sanduiche,
	bebidas : set Bebida,
	doces : set Doce
}

--Cliente pode possuir um ou mais pedidos
sig Cliente {
	pedidos : some Pedido
}

--Lanchonete pode ter zero ou mais clientes
one sig Lanchonete {
	clientes : set Cliente
}

--Qualquer pedido que não seja combo 
sig SemCombo extends Pedido{}

--Combo um: Se tiver dois ou mais salgados ou sanduiches e tiver pedido refrigerante ganha uma torta 
sig ComboUm extends Pedido  {
	brinde : one Doce
}

--Combo dois: Se tiver dois ou mais salgados ou sanduiches e tiver pedido refrigerante ou suco ganha um brigadeiro 
sig ComboDois extends Pedido  {
	brinde : one Torta
}

fun getBrindeComboUm[c1: ComboUm] : one Doce {
	c1.brinde
}

fun getBrindeComboDois[c2: ComboDois] : one Doce {
	c2.brinde
}

fun getDoces[p:Pedido] : set Doce{
	p.doces
}

--Predicados 

pred show[]{
}

--Todo cliente pertence a lanchonete
pred todoClientePertenceALanchonete{
	all c:Cliente | one c.~clientes
}

--Todo pedido está ligado a um cliente
pred todoPedidoPertenceAUmCliente{
	all p:Pedido |  one p.~pedidos
}

--Todo pedido está ligado a um cliente
pred todoProdutoPertenceAUmPedido{
	all sa:Salgado |  one sa.~salgados 
	all sd:Sanduiche |  one sd.~sanduiches
	all be:Bebida |  one be.~bebidas
	all do:Doce |  one do.~doces
}

pred naoTemCombo{
	all sc:SemCombo , r: Refrigerante, s: Suco|  !((#(sc.salgados) >= 2 or #(sc.sanduiches) >= 2) and ((r in sc.bebidas) or (s in sc.bebidas))) 
												and 
								       !(r in sc.bebidas and  ((#(sc.salgados) >= 2 and #(sc.sanduiches) >= 1) or (#(sc.sanduiches) >= 2 and #(sc.salgados) >= 1)))   
}

pred comboUmNaoTemTorta {
	all p:ComboUm, t:Torta |  t != getBrindeComboUm[p]
}

pred brindeNaoEhSobremesa {
	all c:ComboUm | !(getBrindeComboUm[c] in getDoces[c]) 
	all c:ComboDois | !(getBrindeComboDois[c] in getDoces[c]) 
}

pred temCombo{
	all p:ComboUm | one r: Refrigerante, s: Suco|  ((#(p.salgados) >= 2 or #(p.sanduiches) >= 2) and ((r in p.bebidas) or (s in p.bebidas)))
	all p:ComboDois | one  r:Refrigerante |  r in p.bebidas and  ((#(p.salgados) >= 2 and #(p.sanduiches) >= 1) or (#(p.sanduiches) >= 2 and #(p.salgados) >= 1))
}

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


run show for 10 but exactly 4 Cliente, exactly 6 Pedido, exactly 2 ComboDois, exactly 2 ComboUm,  exactly 2 SemCombo
