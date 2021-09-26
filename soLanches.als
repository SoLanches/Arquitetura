module SoLanches


//---------------SIGNATURES---------------

one sig SoLanches {
	-- Conjunto de comercios do sistema.
	comercios: set Comercio
}

sig Comercio {
	cardapio: one Cardapio,
}


sig Cardapio {
	produtos: set Produto
}

sig Produto {
	categoria: one Categoria
}

sig Categoria {}



---------------PRED---------------

-- O comercio esta dentro de uma entidade SoLanches
pred comercioNoSoLanches[c: Comercio, s: SoLanches] {
	c in s.comercios
}



-- O produto pertence aos produtos do cardapio passado
pred produtoNoCardapio[p: Produto, c: Cardapio] {
	p in c.produtos
}

pred cardapioNoComercio[ca: Cardapio, co: Comercio] {
	ca = getCardapioComercio[co]
}


---------------FUNCTIONS---------------

fun getCategoriaProduto[p: Produto]: one Categoria {
	p.categoria
}

fun getCardapioComercio[c: Comercio]: one Cardapio {
	c.cardapio
}




---------------FACTS---------------

-- Todo comercio esta dentro de uma unica entidade do SoLanches
fact todosComerciosNoSoLanches {
	all c: Comercio| one s: SoLanches | comercioNoSoLanches[c, s]
}

-- Todo cardapio esta pertence a um comercio
fact todosCardapiosDentroDeComercio {
	all ca: Cardapio | one co: Comercio | ca = getCardapioComercio[co]
}

-- Todo comercio tem um cardapio
fact todosComerciosTemCardapio {
	all co: Comercio | one ca: Cardapio | ca = getCardapioComercio[co]
}

-- Todo produto esta dentro de um cardapio
fact todosProdutosDentroDeCardapio {
	all p: Produto | one c: Cardapio | produtoNoCardapio[p, c]
}

-- Toda categoria pertence a pelo menos um produto.
fact todaCategoriaDentroDeProduto {
	all c: Categoria | some p: Produto | getCategoriaProduto[p] = c
}


---------------ASSERTS---------------

assert todosComerciosNoSolanches {
	all c: Comercio | one s: SoLanches | comercioNoSoLanches[c, s]
}

assert cardapioUnico {
	all c: Cardapio | all disj co1, co2: Comercio | (cardapioNoComercio[c, co1] => !cardapioNoComercio[c, co2])
}

assert todoProdutoTemCategoria {
	all c: Categoria | some p: Produto | c = getCategoriaProduto[p]
}

assert todoProdutoEmCardapios {
	all p: Produto | one c: Cardapio | produtoNoCardapio[p, c]
}

assert todoComercioTemUmCardapio {
	all co: Comercio | one ca: Cardapio | ca = getCardapioComercio[co]
}


pred show[] {}
run show for 5 Int

check todosComerciosNoSolanches for 10

check cardapioUnico for 10

check todoProdutoTemCategoria for 10

check todoProdutoEmCardapios for 10

check todoComercioTemUmCardapio for 10
