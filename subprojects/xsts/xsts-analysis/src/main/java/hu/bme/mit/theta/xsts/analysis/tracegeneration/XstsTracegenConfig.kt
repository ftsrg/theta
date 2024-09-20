package hu.bme.mit.theta.xsts.analysis.tracegeneration

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.EmptyCex
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.TraceGenerationChecker
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.TraceGenerationResult
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction

class XstsTracegenConfig<S : State, A : Action, P : Prec?> private constructor(
    private val checker: TraceGenerationChecker<S, A, P>,
    private val prec: P
) {
    fun check(): SafetyResult<TraceGenerationResult<S, A>, EmptyCex> {
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
