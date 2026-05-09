package hu.bme.mit.theta.analysis.algorithm.lazy;

import com.google.common.collect.Lists;
import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.algorithm.arg.ARG;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.arg.SearchStrategy;
import hu.bme.mit.theta.analysis.algorithm.cegar.AbstractorResult;
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgAbstractor;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.reachedset.Partition;
import hu.bme.mit.theta.analysis.waitlist.Waitlist;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.utils.Lens;

import java.util.ArrayList;
import java.util.Collection;
import java.util.function.Predicate;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkNotNull;

public final class LazyAbstractor<SConcr extends State, SAbstr extends State, FSConcr extends State, FSAbstr extends ExprState, A extends Action, P extends Prec>
        implements ArgAbstractor<LazyState<FSConcr, FSAbstr>, A, P> {
    private final LTS<FSConcr, A> lts;
    private final SearchStrategy searchStrategy;
    private final LazyStrategy<SConcr, SAbstr, LazyState<FSConcr, FSAbstr>, A> lazyStrategy;
    private final Analysis<LazyState<FSConcr, FSAbstr>, A, P> analysis;
    private final Predicate<FSConcr> isTarget;
    private final Lens<LazyState<FSConcr, FSAbstr>, SConcr> concrStateLens;
    private final Logger logger;

    public LazyAbstractor(final LTS<FSConcr, A> lts,
                          final SearchStrategy searchStrategy,
                          final LazyStrategy<SConcr, SAbstr, LazyState<FSConcr, FSAbstr>, A> lazyStrategy,
                          final LazyAnalysis<FSConcr, FSAbstr, A, P> analysis,
                          final Predicate<FSConcr> isTarget,
                          final Lens<LazyState<FSConcr, FSAbstr>, SConcr> concrStateLens,
                          final Logger logger) {
        this.lts = checkNotNull(lts);
        this.searchStrategy = checkNotNull(searchStrategy);
        this.lazyStrategy = checkNotNull(lazyStrategy);
        this.analysis = checkNotNull(analysis);
        this.isTarget = isTarget;
        this.concrStateLens = concrStateLens;
        this.logger = logger;
    }

    @Override
    public ARG<LazyState<FSConcr, FSAbstr>, A> createProof() {
      return ARG.create(analysis.getPartialOrd());
    }

    @Override
    public LazyAbstractorResult check(ARG<LazyState<FSConcr, FSAbstr>, A> arg, P prec) {
        Waitlist<ArgNode<LazyState<FSConcr, FSAbstr>, A>> waiting = searchStrategy.createWaitlist();
        if (arg.getNodes().findAny().isEmpty()) {
            final Collection<? extends LazyState<FSConcr, FSAbstr>>
                    initStates = analysis.getInitFunc().getInitStates(prec);
            for (final LazyState<FSConcr, FSAbstr> initState : initStates) {
                final boolean target = isTarget.test(initState.getConcrState());
                arg.createInitNode(initState, target);
            }
            waiting.addAll(arg.getInitNodes());
        } else {
            Stream<ArgNode<LazyState<FSConcr, FSAbstr>, A>> incompleteNodes = arg.getIncompleteNodes();
            waiting.addAll(incompleteNodes);
        }
        return new CheckMethod(arg, waiting, prec).run();
    }

    private final class CheckMethod {
        final ARG<LazyState<FSConcr, FSAbstr>, A> arg;
        final P prec;
        final LazyStatistics.Builder stats;
        final Partition<ArgNode<LazyState<FSConcr, FSAbstr>, A>, ?> passed;
        final Waitlist<ArgNode<LazyState<FSConcr, FSAbstr>, A>> waiting;

        public CheckMethod(final ARG<LazyState<FSConcr, FSAbstr>, A> arg,
                           final Waitlist<ArgNode<LazyState<FSConcr, FSAbstr>, A>> waiting,
                           final P prec) {
            this.arg = arg;
            this.prec = prec;
            stats = LazyStatistics.builder(arg);
            passed = Partition.of(n -> lazyStrategy.getProjection().apply(n.getState()));
            this.waiting = waiting;
        }

        public LazyAbstractorResult run() {
            stats.startAlgorithm();

            if (arg.getInitNodes().anyMatch(ArgNode::isTarget)) {
                return stopAlgorithm(false);
            }

            while (!waiting.isEmpty()) {
                final ArgNode<LazyState<FSConcr, FSAbstr>, A> v = waiting.remove();
                assert v.isFeasible();

                close(v, stats);
                if (!v.isCovered()) {
                    boolean isSafe = expand(v, arg, stats);
                    if (!isSafe) {
                        return stopAlgorithm(false);
                    }
                }
            }
            return stopAlgorithm(true);
        }

        private void close(final ArgNode<LazyState<FSConcr, FSAbstr>, A> coveree,
                           final LazyStatistics.Builder stats) {
            stats.startClosing();

            final Iterable<ArgNode<LazyState<FSConcr, FSAbstr>, A>>
                    candidates = Lists.reverse(passed.get(coveree));
            for (final ArgNode<LazyState<FSConcr, FSAbstr>, A> coverer : candidates) {

                stats.checkCoverage();
                if (lazyStrategy.mightCover(coveree, coverer)) {

                    stats.attemptCoverage();

                    coveree.setCoveringNode(coverer);
                    final Collection<ArgNode<LazyState<FSConcr, FSAbstr>, A>>
                            uncoveredNodes = new ArrayList<>();
                    lazyStrategy.cover(coveree, coverer, uncoveredNodes, stats);
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

        private boolean expand(final ArgNode<LazyState<FSConcr, FSAbstr>, A> node,
                            final ARG<LazyState<FSConcr, FSAbstr>, A> arg,
                            final LazyStatistics.Builder stats) {
            stats.startExpanding();
            final LazyState<FSConcr, FSAbstr> state = node.getState();

            for (final A action : lts.getEnabledActionsFor(state.getConcrState())) {
                final Collection<? extends LazyState<FSConcr, FSAbstr>>
                        succStates = analysis.getTransFunc().getSuccStates(state, action, prec);

                for (final LazyState<FSConcr, FSAbstr> succState : succStates) {
                    if (node.getSuccNodes().noneMatch(n -> n.getInEdge().get().getAction().equals(action)
                            && n.getState().equals(succState))) {
                        if (lazyStrategy.inconsistentState(concrStateLens.get(succState))) {
                            final Collection<ArgNode<LazyState<FSConcr, FSAbstr>, A>>
                                    uncoveredNodes = new ArrayList<>();
                            lazyStrategy.disable(node, action, succState, uncoveredNodes, stats);
                            waiting.addAll(uncoveredNodes);
                        } else {
                            final boolean target = isTarget.test(succState.getConcrState());
                            final ArgNode<LazyState<FSConcr, FSAbstr>, A>
                                    succNode = arg.createSuccNode(node, action, succState, target);
                            if (target) {
                                stats.stopExpanding();
                                return false;
                            }
                            waiting.add(succNode);
                        }
                    }
                }
            }
            node.expanded = true;
            passed.add(node);
            stats.stopExpanding();
            return true;
        }

        private LazyAbstractorResult stopAlgorithm(boolean isSafe) {
          stats.stopAlgorithm();
          final LazyStatistics statistics = stats.build();
          final LazyAbstractorResult result = isSafe
              ? LazyAbstractorResult.safe(arg, statistics)
              : LazyAbstractorResult.unsafe(arg.getCexs().findAny().get().toTrace(), arg, statistics);
          logger.write(Logger.Level.BENCHMARK, statistics.toString());
          logger.write(Logger.Level.RESULT, "%s%n", result.toString());
          return result;
        }
    }
}
