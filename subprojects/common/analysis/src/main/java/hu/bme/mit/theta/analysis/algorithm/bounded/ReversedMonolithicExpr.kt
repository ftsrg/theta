package hu.bme.mit.theta.analysis.algorithm.bounded

import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory

fun MonolithicExpr.createReversed(): MonolithicExpr {
    return MonolithicExpr(
        initExpr = Not(propExpr),
        transExpr = ExprUtils.reverse(transExpr, transOffsetIndex),
        propExpr = Not(initExpr),
        transOffsetIndex = transOffsetIndex,
        initOffsetIndex = VarIndexingFactory.indexing(0),
        vars = vars
    )
}