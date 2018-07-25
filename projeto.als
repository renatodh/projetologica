module lanchonete

--Assinaturas
abstract sig Salgado {}
abstract sig Sanduiche {}
abstract sig Bebida {}
abstract sig Doce {}

one sig Coxinha,Empada,Pastel extends Salgado {}
one sig SanduicheFrango,SanduicheAtum extends Sanduiche {}
one sig Agua,Refrigerante,Suco extends Bebida {}
one sig Pudim, Brigadeiro,Torta extends Doce {}

abstract sig Pedido{}

--Pedido pode ter salgados, sanduiches, bebidas e doces 
sig PedidoComum extends Pedido{
	salgados : set Salgado,
	sanduiches : set Sanduiche,
	bebidas : set Bebida,
	doces : set Doce
}

--Pedido que contem o brinde do cliente
sig PedidoBonificado extends Pedido{
	brinde : one Doce
}

--Cliente pode possuir um ou mais pedidos
sig Cliente {
	pedidos : some Pedido
}

--Predicados 

--Todo pedido está ligado a um cliente
pred todoPedidoPerteceAUmCliente{
	all p:Pedido |  one p.~pedidos
}

--Tem dois ou mais salgados no pedido
pred doisOuMaisSalgados[p:Pedido]{
	all p : Pedido | (#p.salgados) > 1
}

--Tem dois ou mais sanduiches no pedido
pred doisOuMaisSanduiches[p:Pedido]{
	all p : Pedido | (#p.sanduiches) > 1
}

--Tem uma bebida que nao eh agua no pedido
pred naoPediuAgua[p:Pedido] {
	all p : Pedido | some b : Agua |  !(b in p.bebidas)
}

--Tem refrigerante no pedido 
pred pediuRefrigerante[p:Pedido]{
	all p: Pedido | some b:Refrigerante | b in p.bebidas
}

pred show[]{
}

--Fatos

fact{
	todoPedidoPertenceAUmCliente
}

--Funções

--Retorna os pedidos do cliente
fun getPedidosCliente[c: Cliente]: Pedido {
	c.pedidos
}

--Retorna o brinde do cliente
fun getBrindeCliente[c: Cliente]: Doce{
	c.brinde
}

--Asserts



run show for 3
