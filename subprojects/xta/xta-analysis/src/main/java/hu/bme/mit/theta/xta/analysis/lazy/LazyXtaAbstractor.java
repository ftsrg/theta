package hu.bme.mit.theta.xta.analysis.lazy;

import com.google.common.collect.Lists;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.SearchStrategy;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.AbstractorResult;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyStrategy;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyAnalysis;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState;
import hu.bme.mit.theta.analysis.reachedset.Partition;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.waitlist.Waitlist;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaLts;
import hu.bme.mit.theta.xta.analysis.XtaState;

import java.util.ArrayList;
import java.util.Collection;

import static com.google.common.base.Preconditions.checkNotNull;

public final class LazyXtaAbstractor<SConcr extends State, SAbstr extends State, P extends Prec>
        implements Abstractor<LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction, UnitPrec> {
    private final XtaLts lts;
    private final SearchStrategy searchStrategy;
    private final LazyStrategy<SConcr, SAbstr, LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction> lazyStrategy;
    private final Analysis<LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction, P> analysis;
    private final P prec;

    private static int argNo = 0;

    public LazyXtaAbstractor(final XtaSystem system,
                             final SearchStrategy searchStrategy,
                             final LazyStrategy<SConcr, SAbstr, LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction> lazyStrategy,
                             final LazyAnalysis<XtaState<SConcr>, XtaState<SAbstr>, XtaAction, P> analysis,
                             final P prec) {
        checkNotNull(system);
        this.lts = XtaLts.create(system);
        this.searchStrategy = checkNotNull(searchStrategy);
        this.lazyStrategy = checkNotNull(lazyStrategy);
        this.analysis = checkNotNull(analysis);
        this.prec = checkNotNull(prec);
    }

    @Override
    public ARG<LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction> createArg() {
        final ARG<LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction> arg = ARG.create(analysis.getPartialOrd());
        final Collection<? extends LazyState<XtaState<SConcr>, XtaState<SAbstr>>>
                initStates = analysis.getInitFunc().getInitStates(prec);
        for (final LazyState<XtaState<SConcr>, XtaState<SAbstr>> initState : initStates) {
            final boolean target = initState.getConcrState().isError();
            arg.createInitNode(initState, target);
        }
        return arg;
    }

    @Override
    public AbstractorResult check(ARG<LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction> arg, UnitPrec prec) {
        return new CheckMethod(arg).run();
    }

    private final class CheckMethod {
        final ARG<LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction> arg;
        final LazyXtaStatistics.Builder stats;
        final Partition<ArgNode<LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction>, ?> passed;
        final Waitlist<ArgNode<LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction>> waiting;


        public CheckMethod(final ARG<LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction> arg) {
            this.arg = arg;
            stats = LazyXtaStatistics.builder(arg);
            passed = Partition.of(n -> lazyStrategy.getProjection().apply(n.getState()));
            waiting = searchStrategy.createWaitlist();
        }

        public AbstractorResult run() {
            stats.startAlgorithm();

            if (arg.getInitNodes().anyMatch(ArgNode::isTarget)) {
                return stop(AbstractorResult.unsafe());
            }

            waiting.addAll(arg.getInitNodes());
            while (!waiting.isEmpty()) {
                final ArgNode<LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction> v = waiting.remove();
                assert v.isFeasible();

                close(v, stats);
                if (!v.isCovered()) {
                    AbstractorResult result = expand(v, arg, stats);
                    if (result.isUnsafe()) {
                        return stop(AbstractorResult.unsafe());
                    }
                }
            }

            return stop(AbstractorResult.safe());
        }

        private AbstractorResult stop(AbstractorResult result) {
            stats.stopAlgorithm();
            final LazyXtaStatistics statistics = stats.build();
            return result;
        }

        private void close(final ArgNode<LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction> coveree,
                           final LazyXtaStatistics.Builder stats) {
            stats.startClosing();

            final Iterable<ArgNode<LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction>>
                    candidates = Lists.reverse(passed.get(coveree));
            for (final ArgNode<LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction> coverer : candidates) {

                stats.checkCoverage();
                if (lazyStrategy.mightCover(coveree, coverer)) {

                    stats.attemptCoverage();

                    coveree.setCoveringNode(coverer);
                    final Collection<ArgNode<LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction>>
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

        private AbstractorResult expand(final ArgNode<LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction> node,
                            final ARG<LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction> arg,
                            final LazyXtaStatistics.Builder stats) {
            stats.startExpanding();
            final LazyState<XtaState<SConcr>, XtaState<SAbstr>> state = node.getState();

            for (final XtaAction action : lts.getEnabledActionsFor(state.getConcrState())) {
                final Collection<? extends LazyState<XtaState<SConcr>, XtaState<SAbstr>>>
                        succStates = analysis.getTransFunc().getSuccStates(state, action, prec);

                for (final LazyState<XtaState<SConcr>, XtaState<SAbstr>> succState : succStates) {
                    if (succState.isBottom()) {
                        final Collection<ArgNode<LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction>>
                                uncoveredNodes = new ArrayList<>();
                        lazyStrategy.disable(node, action, succState, uncoveredNodes);
                        waiting.addAll(uncoveredNodes);
                    } else {
                        final boolean target = succState.getConcrState().isError();
                        final ArgNode<LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction>
                                succNode = arg.createSuccNode(node, action, succState, target);
                        if (target) {
                            stats.stopExpanding();
                            return AbstractorResult.unsafe();
                        }
                        waiting.add(succNode);
                    }
                }
            }
            passed.add(node);
            stats.stopExpanding();
            return AbstractorResult.safe();
        }
    }
}
