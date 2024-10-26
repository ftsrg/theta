package hu.bme.mit.theta.xsts.analysis.tracegeneration

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.TraceGenerationChecker
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary.TraceGenerationResult
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary.AbstractTraceSummary
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState

class XstsTracegenConfig<S : State, A : Action, P : Prec> private constructor(
    private val checker: TraceGenerationChecker<S, A, P>,
    private val prec: P
) {
    fun check(): TraceGenerationResult<AbstractTraceSummary<S, A>, S, A> {
        return checker.check(prec)
    }

    companion object {
        fun <S : State, A : Action, P : Prec> create(
            checker: TraceGenerationChecker<S, A, P>, initPrec: P
        ): XstsTracegenConfig<S, A, P> {
            return XstsTracegenConfig(checker, initPrec)
        }
    }
}
