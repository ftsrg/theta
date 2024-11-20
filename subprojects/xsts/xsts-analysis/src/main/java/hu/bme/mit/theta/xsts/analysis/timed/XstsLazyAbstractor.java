package hu.bme.mit.theta.xsts.analysis.timed;

import com.google.common.collect.Lists;
import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.SearchStrategy;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.AbstractorResult;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyAnalysis;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyStatistics;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyStrategy;
import hu.bme.mit.theta.analysis.algorithm.runtimecheck.AbstractArg;
import hu.bme.mit.theta.analysis.algorithm.runtimecheck.ArgCexCheckHandler;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.reachedset.Partition;
import hu.bme.mit.theta.analysis.waitlist.Waitlist;
import hu.bme.mit.theta.xsts.analysis.XstsAction;
import hu.bme.mit.theta.xsts.analysis.XstsState;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Optional;
import java.util.function.Predicate;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkNotNull;

public final class XstsLazyAbstractor<SConcr extends ExprState, SAbstr extends ExprState, P extends Prec>
        implements Abstractor<LazyState<XstsState<SConcr>, XstsState<SAbstr>>, XstsAction, P> {

    private final ControlFlowSplitXstsLts<SConcr> lts;
    private final SearchStrategy searchStrategy;
    private final LazyStrategy<SConcr, SAbstr, LazyState<XstsState<SConcr>, XstsState<SAbstr>>, XstsAction> lazyStrategy;
    private final Analysis<LazyState<XstsState<SConcr>, XstsState<SAbstr>>, XstsAction, P> analysis;
    private final Predicate<XstsState<SConcr>> isTarget;
    private final boolean feasibleActionsOnly;

    public XstsLazyAbstractor(final ControlFlowSplitXstsLts<SConcr> lts,
                              final SearchStrategy searchStrategy,
                              final LazyStrategy<SConcr, SAbstr, LazyState<XstsState<SConcr>, XstsState<SAbstr>>, XstsAction> lazyStrategy,
                              final LazyAnalysis<XstsState<SConcr>, XstsState<SAbstr>, XstsAction, P> analysis,
                              final Predicate<XstsState<SConcr>> isTarget,
                              final boolean feasibleActionsOnly) {
        this.lts = checkNotNull(lts);
        this.searchStrategy = checkNotNull(searchStrategy);
        this.lazyStrategy = checkNotNull(lazyStrategy);
        this.analysis = checkNotNull(analysis);
        this.isTarget = isTarget;
        this.feasibleActionsOnly = feasibleActionsOnly;
    }

    @Override
    public ARG<LazyState<XstsState<SConcr>, XstsState<SAbstr>>, XstsAction> createArg() {
        return ARG.create(analysis.getPartialOrd());
    }

    @Override
    public AbstractorResult check(ARG<LazyState<XstsState<SConcr>, XstsState<SAbstr>>, XstsAction> arg, P prec) {
        Waitlist<ArgNode<LazyState<XstsState<SConcr>, XstsState<SAbstr>>, XstsAction>> waiting = searchStrategy.createWaitlist();
        final Collection<? extends LazyState<XstsState<SConcr>, XstsState<SAbstr>>>
                initStates = analysis.getInitFunc().getInitStates(prec);
        if (arg.getInitNodes().count() < initStates.size()) {
            for (final LazyState<XstsState<SConcr>, XstsState<SAbstr>> initState : initStates) {
                final boolean target = isTarget.test(initState.getConcrState());
                arg.createInitNode(initState, target);
            }
            waiting.addAll(arg.getInitNodes());
        } else {
            Stream<ArgNode<LazyState<XstsState<SConcr>, XstsState<SAbstr>>, XstsAction>> incompleteNodes = arg.getIncompleteNodes();
            waiting.addAll(incompleteNodes);
        }
        ArgCexCheckHandler.instance.setCurrentArg(new AbstractArg<>(arg, prec));
        return new CheckMethod(arg, waiting, prec).run();
    }

    private final class CheckMethod {
        final ARG<LazyState<XstsState<SConcr>, XstsState<SAbstr>>, XstsAction> arg;
        final P prec;
        final LazyStatistics.Builder stats;
        final Partition<ArgNode<LazyState<XstsState<SConcr>, XstsState<SAbstr>>, XstsAction>, ?> passed;
        final Waitlist<ArgNode<LazyState<XstsState<SConcr>, XstsState<SAbstr>>, XstsAction>> waiting;

        public CheckMethod(final ARG<LazyState<XstsState<SConcr>, XstsState<SAbstr>>, XstsAction> arg,
                           final Waitlist<ArgNode<LazyState<XstsState<SConcr>, XstsState<SAbstr>>, XstsAction>> waiting,
                           final P prec) {
            this.arg = arg;
            this.prec = prec;
            stats = LazyStatistics.builder(arg);
            passed = Partition.of(n -> lazyStrategy.getProjection().apply(n.getState()));
            this.waiting = waiting;
        }

        public AbstractorResult run() {
            stats.startAlgorithm();

            if (arg.getInitNodes().anyMatch(ArgNode::isTarget)) {
                return stop(AbstractorResult.unsafe());
            }

            while (!waiting.isEmpty()) {
                final ArgNode<LazyState<XstsState<SConcr>, XstsState<SAbstr>>, XstsAction> v = waiting.remove();
                assert v.isFeasible();

                close(v, stats);
                if (!v.isCovered()) {
                    AbstractorResult result = expand(v, arg, stats);
                    if (result.isUnsafe()) {
                        return stop(AbstractorResult.unsafe());
                    }
                }
                ArgCexCheckHandler.instance.setCurrentArg(new AbstractArg<>(arg, prec));
            }
            return stop(AbstractorResult.safe());
        }

        private AbstractorResult stop(AbstractorResult result) {
            stats.stopAlgorithm();
            final LazyStatistics statistics = stats.build();
            return result;
        }

        private void close(final ArgNode<LazyState<XstsState<SConcr>, XstsState<SAbstr>>, XstsAction> coveree,
                           final LazyStatistics.Builder stats) {
            stats.startClosing();

            final Iterable<ArgNode<LazyState<XstsState<SConcr>, XstsState<SAbstr>>, XstsAction>>
                    candidates = Lists.reverse(passed.get(coveree));
            for (final ArgNode<LazyState<XstsState<SConcr>, XstsState<SAbstr>>, XstsAction> coverer : candidates) {

                stats.checkCoverage();
                if (lazyStrategy.mightCover(coveree, coverer)) {

                    stats.attemptCoverage();

                    coveree.setCoveringNode(coverer);
                    final Collection<ArgNode<LazyState<XstsState<SConcr>, XstsState<SAbstr>>, XstsAction>>
                            uncoveredNodes = new ArrayList<>();
                    lazyStrategy.cover(coveree, coverer, uncoveredNodes);
                    waiting.addAll(uncoveredNodes.stream().filter(n -> !n.equals(coveree)));

                    if (coveree.isCovered()) {
                        stats.successfulCoverage();
                        stats.stopClosing();
                        return;
                    }
                }
            }

            stats.stopClosing();
        }

        private AbstractorResult expand(final ArgNode<LazyState<XstsState<SConcr>, XstsState<SAbstr>>, XstsAction> node,
                            final ARG<LazyState<XstsState<SConcr>, XstsState<SAbstr>>, XstsAction> arg,
                            final LazyStatistics.Builder stats) {
            stats.startExpanding();
            final LazyState<XstsState<SConcr>, XstsState<SAbstr>> state = node.getState();

            lts.reset();
            lts.splitControlFlows(state.getConcrState(), feasibleActionsOnly);
            if (feasibleActionsOnly) {
                lts.updateSourceAbstractState(state.getAbstrState());
            }
            Optional<XstsAction> nextAction = lts.getNextEnabledAction();

            while (nextAction.isPresent()) {
                final XstsAction action = nextAction.get();

                final Collection<? extends LazyState<XstsState<SConcr>, XstsState<SAbstr>>>
                        succStates = analysis.getTransFunc().getSuccStates(state, action, prec);

                for (final LazyState<XstsState<SConcr>, XstsState<SAbstr>> succState : succStates) {
                    if (node.getSuccNodes().noneMatch(n -> n.getInEdge().get().getAction().equals(action)
                            && n.getState().equals(succState))) {
                        if (lazyStrategy.inconsistentState(succState)) {
                            final Collection<ArgNode<LazyState<XstsState<SConcr>, XstsState<SAbstr>>, XstsAction>>
                                    uncoveredNodes = new ArrayList<>();
                            lazyStrategy.disable(node, action, succState, uncoveredNodes);
                            waiting.addAll(uncoveredNodes);

                            if (feasibleActionsOnly) {
                                lts.updateSourceAbstractState(node.getState().getAbstrState());
                            }
                        } else {
                            final boolean target = isTarget.test(succState.getConcrState());
                            final ArgNode<LazyState<XstsState<SConcr>, XstsState<SAbstr>>, XstsAction>
                                    succNode = arg.createSuccNode(node, action, succState, target);
                            if (target) {
                                stats.stopExpanding();
                                return AbstractorResult.unsafe();
                            }
                            waiting.add(succNode);
                        }
                    }
                }

                nextAction = lts.getNextEnabledAction();
            }

            node.expanded = true;
            passed.add(node);
            stats.stopExpanding();
            return AbstractorResult.safe();
        }
    }
}
