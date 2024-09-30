package hu.bme.mit.theta.analysis.algorithm.bounded

import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.anytype.Exprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.IffExpr
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory

fun MonolithicExpr.createAbstract(prec: PredPrec): MonolithicExpr {
    // TODO: handle initOffsetIndex in abstract initExpr
    val lambdaList = ArrayList<IffExpr>()
    val lambdaPrimeList = ArrayList<IffExpr>()
    val activationLiterals = ArrayList<VarDecl<*>>()
    prec.preds.forEachIndexed { index, expr ->
        run {
            val v = Decls.Var("v$index", BoolType.getInstance())
            activationLiterals.add(v)
            lambdaList.add(IffExpr.of(v.ref, expr))
            lambdaPrimeList.add(BoolExprs.Iff(Exprs.Prime(v.ref), ExprUtils.applyPrimes(expr, this.transOffsetIndex)))
        }
    }

    var indexingBuilder = VarIndexingFactory.indexingBuilder(1)
    this.vars.forEach { decl ->
        repeat(transOffsetIndex.get(decl)) {
            indexingBuilder = indexingBuilder.inc(decl)
        }
    }

    return MonolithicExpr(
        initExpr = And(And(lambdaList), initExpr),
        transExpr = And(And(lambdaList), And(lambdaPrimeList), transExpr),
        propExpr = Not(And(And(lambdaList), Not(propExpr))),
        transOffsetIndex = indexingBuilder.build(),
        initOffsetIndex = VarIndexingFactory.indexing(0),
        vars = activationLiterals
    )
}