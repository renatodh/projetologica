module lanchonete

--Assinaturas

abstract sig Salgado {}
abstract sig Sanduiche {}
abstract sig Bebida {}
abstract sig Doce {}

sig Coxinha,Empada,Pastel extends Salgado {}
sig SanduicheFrango,SanduicheAtum extends Sanduiche {}
sig Agua,Refrigerante,Suco extends Bebida {}
sig Pudim, Brigadeiro,Torta extends Doce {}

abstract sig Pedido{
	salgados : some Salgado,
	sanduiches : some Sanduiche,
	bebidas : some Bebida,
	doces : some Doce
}

--Combo um: Se tiver dois ou mais salgados ou sanduiches e tiver pedido refrigerante ganha uma torta 
sig ComboUm extends Pedido{
	brinde : one Torta
}

--Combo dois: Se tiver dois ou mais salgados ou sanduiches e tiver pedido refrigerante ou suco ganha um brigadeiro 
sig ComboDois extends Pedido{
	brinde : one Brigadeiro
}

--Combo tres: Se tiver dois ou mais salgados ou sanduiches e tiver pedido refrigerante ou suco ganha um pudim
sig ComboTres extends Pedido{
	brinde : one Pudim
}

--Qualquer pedido que não seja combo 
sig SemCombo extends Pedido{
}

--Cliente pode possuir um ou mais pedidos
sig Cliente {
	pedidos : some Pedido
}

--Lanchonete pode ter zero ou mais clientes
one sig Lanchonete{
	clientes : set Cliente
}

--Predicados 

pred show[]{
}

--Pedido sem combo nao possui dois sanduiches ou salgados ou nao possui refrigerante ou suco
pred naoTemCombo[]{
	all p : SemCombo , r: Refrigerante, s: Suco| #(p.salgados) < 2 and #(p.sanduiches) < 2 
				   					or ! (r in p.bebidas) and !(s in p.bebidas)			   
}

--Todo pedido está ligado a um cliente
pred todoPedidoPertenceAUmCliente[]{
	all p:Pedido |  one p.~pedidos
}

--Todo cliente pertence a lanchonete
pred todoClientePertenceALanchonete[]{
	all c:Cliente | one c.~clientes
}

--Todo combo tem dois ou mais sanduiches ou salgados
pred todoComboTemDois[]{
	all c1:ComboUm | (#(c1.salgados) = 2 and  #(c1.sanduiches) >=1)  or  (#(c1.sanduiches) = 2 and #(c1.salgados) >= 1) or #(c1.salgados) > 2 or  #(c1.sanduiches) > 2
	all c2:ComboDois | #(c2.salgados) >= 2 or  #(c2.sanduiches) >= 2
	all c3:ComboTres | #(c3.salgados) >= 2 or  #(c3.sanduiches) >= 2
}

--Combos dois e tres nao pediram agua
pred naoPediuAgua[]{
	all c2:ComboDois, a : Agua |  !(a in c2.bebidas) 
	all c3:ComboTres, a : Agua |  !(a in c3.bebidas) 
}

--Combo um pediu refrigerante
pred pediuRefrigerante[]{
	all c1:ComboUm, r:Refrigerante |  r in c1.bebidas
}

--Fatos

fact {
	todoComboTemDois[]
	naoPediuAgua[]
	pediuRefrigerante[]
	todoPedidoPertenceAUmCliente[]
	naoTemCombo[]
	todoClientePertenceALanchonete[]
	
}

--Asserts


assert pedidoTemTortaBrinde{
	all p:Pedido , t : Torta, r:Refrigerante | t in p.brinde => (#p.salgados > 2 or #p.sanduiches > 2 or 
							(#(p.salgados) = 2 and  #(p.sanduiches) >=1)  or  
							(#(p.sanduiches) = 2 and #(p.salgados) >= 1)  and r in p.bebidas) 
}

assert pedidoTemBrigadeiroBrinde{
	all p:Pedido , b:Brigadeiro, s: Suco, r:Refrigerante | b in p.brinde => (#p.salgados >= 2 or #p.sanduiches >= 2)
												 and (s in p.bebidas or r in p.bebidas)
}

assert pedidoTemPudimBrinde{
	all p:Pedido , pu:Pudim, s: Suco, r:Refrigerante | pu in p.brinde => (#p.salgados >= 2 or #p.sanduiches >= 2)
												 and (s in p.bebidas or r in p.bebidas)
}

check pedidoTemTortaBrinde for 3
check pedidoTemBrigadeiroBrinde for 3
check pedidoTemPudimBrinde for 3

run show for 3
