package hu.bme.mit.theta.analysis.algorithm.bounded

import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.Exprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.IffExpr
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory

class AbstractMonolithicExpr(monolithicExpr: MonolithicExpr, prec: PredPrec): MonolithicExpr {

    private val vars: Collection<VarDecl<*>>
    private val initExpr: Expr<BoolType>
    private val transExpr: Expr<BoolType>
    private val propExpr: Expr<BoolType>
    private val offsetIndexing: VarIndexing

    init {
        val lambdaList = ArrayList<IffExpr>()
        val lambdaPrimeList = ArrayList<IffExpr>()
        val vars = ArrayList<VarDecl<*>>()
        prec.preds.forEachIndexed{
            index, expr ->
            run {
                val v = Decls.Var("v$index", BoolType.getInstance())
                vars.add(v)
                lambdaList.add(IffExpr.of(v.ref, expr))
                lambdaPrimeList.add(BoolExprs.Iff(Exprs.Prime(v.ref), ExprUtils.applyPrimes(expr, VarIndexingFactory.indexing(1))))
            }
        }

        var indexingBuilder = VarIndexingFactory.indexingBuilder(1)
        monolithicExpr.vars().forEach {
            indexingBuilder = indexingBuilder.inc(it)
        }
        this.offsetIndexing = indexingBuilder.build()

        this.vars = vars
        this.initExpr = And(And(lambdaList), monolithicExpr.init())
        this.transExpr = And(And(lambdaList), And(lambdaPrimeList), monolithicExpr.trans())
        this.propExpr = Not(And(And(lambdaList), Not(monolithicExpr.prop())))
    }

    override fun init(): Expr<BoolType> = initExpr

    override fun trans(): Expr<BoolType> = transExpr

    override fun prop(): Expr<BoolType> = propExpr

    override fun offsetIndex(): VarIndexing = offsetIndexing

    override fun vars(): Collection<VarDecl<*>> = vars


}