package hu.bme.mit.theta.xsts.analysis.tracegeneration

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.TraceGenerationChecker
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction

class XstsTracegenConfig<S : ExprState?, A : ExprAction?, P : Prec?> private constructor(
    private val checker: TraceGenerationChecker<S, A, P>,
    private val prec: P
) {
    fun check(): SafetyResult<S, A> {
        return checker.check(prec)
    }

    companion object {
        fun <S : ExprState?, A : StmtAction?, P : Prec?> create(
            checker: TraceGenerationChecker<S, A, P>, initPrec: P
        ): XstsTracegenConfig<S, A, P> {
            return XstsTracegenConfig(checker, initPrec)
        }
    }
}
