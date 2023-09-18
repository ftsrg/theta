package hu.bme.mit.theta.xcfa.analysis

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder
import hu.bme.mit.theta.analysis.algorithm.ArgNode
import hu.bme.mit.theta.analysis.algorithm.cegar.BasicAbstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterion
import hu.bme.mit.theta.analysis.waitlist.Waitlist
import hu.bme.mit.theta.common.logging.Logger
import java.util.function.Function

class XcfaAbstractor<S : State, A : Action, P : Prec>(
    argBuilder: ArgBuilder<S, A, P>,
    projection: Function<in S?, *>?,
    waitlist: Waitlist<ArgNode<S, A>>,
    stopCriterion: StopCriterion<S, A>,
    logger: Logger,
) : BasicAbstractor<S, A, P>(argBuilder, projection, waitlist, stopCriterion, logger) {

    override fun close(node: ArgNode<S, A>, candidates: Collection<ArgNode<S, A>>) {
        if (!node.isLeaf) {
            return
        }
        for (candidate in candidates) {
            if (candidate.mayCover(node)) {
                var popped = false
                (node.state as XcfaState<*>).processes.forEach { (pid: Int?, proc: XcfaProcessState) ->
                    if (proc != (candidate.state as XcfaState<*>).processes[pid]) {
                        proc.locs.pop()
                        popped = true
                    }
                }
                if (!popped) node.cover(candidate)
                return
            }
        }
    }

    companion object{
        fun<S : State, A : Action, P : Prec> builder(argBuilder: ArgBuilder<S, A, P>): BasicAbstractor.Builder<S, A, P> {
            return Builder(argBuilder)
        }
    }

    class Builder<S : State, A : Action, P : Prec>(argBuilder: ArgBuilder<S, A, P>)
        : BasicAbstractor.Builder<S, A, P>(argBuilder) {
        override fun build(): BasicAbstractor<S, A, P> {
            return XcfaAbstractor(argBuilder, projection, waitlist, stopCriterion, logger)
        }
    }
}
