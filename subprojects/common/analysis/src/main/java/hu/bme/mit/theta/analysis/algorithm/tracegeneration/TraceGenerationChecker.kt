package hu.bme.mit.theta.analysis.algorithm.tracegeneration

import com.google.common.base.Preconditions
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.*
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.utils.ArgVisualizer
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter
import java.util.function.Consumer

class TraceGenerationChecker<S : ExprState?, A : ExprAction?, P : Prec?>(
    private val logger: Logger,
    private val abstractor: Abstractor<S, A, P>,
) : SafetyChecker<S, A, P> {
    private var traces: List<Trace<S, A>> = ArrayList()

    companion object {
        fun <S : ExprState?, A : ExprAction?, P : Prec?> create(
            logger: Logger,
            abstractor: Abstractor<S, A, P>,
        ): TraceGenerationChecker<S, A, P> {
            return TraceGenerationChecker(logger, abstractor)
        }
    }

    override fun check(prec: P): SafetyResult<S, A> {
        val arg = abstractor.createArg()
        abstractor.check(arg, prec)
        logger.write(Logger.Level.INFO, "Printing ARG..." + System.lineSeparator())
        val g = ArgVisualizer.getDefault().visualize(arg)
        logger.write(
            Logger.Level.INFO,
            GraphvizWriter.getInstance().writeString(g) + System.lineSeparator()
        )

        // bad node: XSTS specific thing, that the last state (last_env nodes) doubles up and the leaf is covered by the
        // last_env before which is superfluous.
        // Possible side effect if not handled: possibly a "non-existing leaf" and superfluous traces or just traces that are 1 longer than they should be
        //val badNodes = XstsDoubleEndNodeRemover.collectBadLeaves(arg)

        // leaves
        val endNodes = arg.nodes.filter { obj: ArgNode<S, A> -> obj.isLeaf }
            .toList()
        // leaves, but bad nodes are properly filtered, see bad nodes above
        //val filteredEndNodes = filterEndNodes(endNodes, badNodes)

        /*val argTraces: List<ArgTrace<S, A>> =
            ArrayList(filteredEndNodes.stream().map { node: ArgNode<S, A>? ->
                ArgTrace.to(
                    node
                )
            }.toList())
        */

        val argTraces: List<ArgTrace<S, A>> =
            ArrayList(endNodes.stream().map { node: ArgNode<S, A>? ->
                ArgTrace.to(
                    node
                )
            }.toList())

        ArrayList(argTraces.stream().map { obj: ArgTrace<S, A> -> obj.toTrace() }
                .toList())

        traces = ArrayList(argTraces.stream().map { obj: ArgTrace<S, A> -> obj.toTrace() }
                .toList())

        Preconditions.checkState(
            traces.isNotEmpty(),
            "Generated 0 traces, configuration should probably be adjusted"
        )
        return SafetyResult.traces(traces)

    }

    private fun filterEndNodes(
        endNodes: List<ArgNode<S, A>>,
        badNodes: List<ArgNode<S, A>>
    ): List<ArgNode<S, A>> {
        val filteredEndNodes: MutableList<ArgNode<S, A>> =
            ArrayList() // leaves that are not "bad nodes" or bad nodes' grandparents
        endNodes.forEach(Consumer { endNode: ArgNode<S, A> ->
            if (badNodes.contains(endNode)) {
                if (endNode.parent.isPresent && endNode.parent.get().parent
                        .isPresent
                ) {
                    val parent =
                        endNode.parent.get()
                    val grandParent =
                        endNode.parent.get().parent.get()
                    // If the parent & grandparent (same state as the bad node) has no other successors,
                    // the grandparent is the "new leaf"
                    // if there are successors, there is no real leaf here
                    if (grandParent.outEdges.count() == 1L && parent.outEdges
                            .count() == 1L
                    ) {
                        filteredEndNodes.add(grandParent)
                    }
                } else {
                    throw RuntimeException("Unexpected error: bad nodes should always have parents and grandparents")
                }
            } else {
                filteredEndNodes.add(endNode)
            }
        })
        return filteredEndNodes
    }
}