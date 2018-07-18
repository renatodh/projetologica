module lanchonete

sig Lanchonete {
	pedidos : set Pedido	
}

sig Pedido {
	salgados : set Salgado,
	sanduiches : set Sanduiche,
	bebidas : set Bebida,
	doces : set Doce
}

sig PedidoBonificado extends Pedido {}

sig Salgado {}
sig Sanduiche {}
sig Bebida {}
sig Doce {}

sig Coxinha,Empada,Pastel extends Salgado {}
sig SandFrango,SandAtum extends Sanduiche {}
sig Agua,Refrigerante,Suco extends Bebida {}
sig Pudim,Torta,Brigadeiro extends Doce {}

fact Bonificacao1 {
	
}


