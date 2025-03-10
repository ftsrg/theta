/*
 *  Copyright 2025 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.arg.ARG;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterion;
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterions;
import hu.bme.mit.theta.analysis.reachedset.Partition;
import hu.bme.mit.theta.analysis.waitlist.FifoWaitlist;
import hu.bme.mit.theta.analysis.waitlist.Waitlist;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.Logger.Level;
import hu.bme.mit.theta.common.logging.NullLogger;
import java.util.Collection;
import java.util.Collections;
import java.util.function.Function;

/** Basic implementation for the abstractor, relying on an ArgBuilder. */
public class BasicArgAbstractor<S extends State, A extends Action, P extends Prec>
        implements ArgAbstractor<S, A, P> {

    protected final ArgBuilder<S, A, P> argBuilder;
    protected final Function<? super S, ?> projection;
    protected final Waitlist<ArgNode<S, A>> waitlist;
    protected final StopCriterion<S, A> stopCriterion;
    protected final Logger logger;

    protected BasicArgAbstractor(
            final ArgBuilder<S, A, P> argBuilder,
            final Function<? super S, ?> projection,
            final Waitlist<ArgNode<S, A>> waitlist,
            final StopCriterion<S, A> stopCriterion,
            final Logger logger) {
        this.argBuilder = checkNotNull(argBuilder);
        this.projection = checkNotNull(projection);
        this.waitlist = checkNotNull(waitlist);
        this.stopCriterion = checkNotNull(stopCriterion);
        this.logger = checkNotNull(logger);
    }

    public static <S extends State, A extends Action, P extends Prec> Builder<S, A, P> builder(
            final ArgBuilder<S, A, P> argBuilder) {
        return new Builder<>(argBuilder);
    }

    @Override
    public ARG<S, A> createProof() {
        return argBuilder.createArg();
    }

    @Override
    public AbstractorResult check(final ARG<S, A> arg, final P prec) {
        checkNotNull(arg);
        checkNotNull(prec);
        logger.write(Level.DETAIL, "|  |  Precision: %s%n", prec);

        if (!arg.isInitialized()) {
            logger.write(Level.SUBSTEP, "|  |  (Re)initializing ARG...");
            argBuilder.init(arg, prec);
            logger.write(Level.SUBSTEP, "done%n");
        }

        assert arg.isInitialized();

        logger.write(
                Level.INFO,
                "|  |  Starting ARG: %d nodes, %d incomplete, %d unsafe%n",
                arg.getNodes().count(),
                arg.getIncompleteNodes().count(),
                arg.getUnsafeNodes().count());
        logger.write(Level.SUBSTEP, "|  |  Building ARG...");

        final Partition<ArgNode<S, A>, ?> reachedSet =
                Partition.of(n -> projection.apply(n.getState()));
        waitlist.clear();

        reachedSet.addAll(arg.getNodes());
        waitlist.addAll(arg.getIncompleteNodes());

        if (!stopCriterion.canStop(arg)) {
            while (!waitlist.isEmpty()) {
                final ArgNode<S, A> node = waitlist.remove();

                Collection<ArgNode<S, A>> newNodes = Collections.emptyList();
                close(node, reachedSet.get(node));
                if (!node.isSubsumed() && !node.isTarget()) {
                    newNodes = argBuilder.expand(node, prec);
                    reachedSet.addAll(newNodes);
                    waitlist.addAll(newNodes);
                }

                if (stopCriterion.canStop(arg, newNodes)) break;
            }
        }

        logger.write(Level.SUBSTEP, "done%n");
        logger.write(
                Level.INFO,
                "|  |  Finished ARG: %d nodes, %d incomplete, %d unsafe%n",
                arg.getNodes().count(),
                arg.getIncompleteNodes().count(),
                arg.getUnsafeNodes().count());

        waitlist.clear(); // Optimization

        if (arg.isSafe()) {
            checkState(arg.isComplete(), "Returning incomplete ARG as safe");
            return AbstractorResult.safe();
        } else {
            return AbstractorResult.unsafe();
        }
    }

    protected void close(final ArgNode<S, A> node, final Collection<ArgNode<S, A>> candidates) {
        if (!node.isLeaf()) {
            return;
        }
        for (final ArgNode<S, A> candidate : candidates) {
            if (candidate.mayCoverStandard(node)) {
                node.cover(candidate);
                return;
            }
        }
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder(getClass().getSimpleName()).add(waitlist).toString();
    }

    public static class Builder<S extends State, A extends Action, P extends Prec> {
        protected final ArgBuilder<S, A, P> argBuilder;
        protected Function<? super S, ?> projection;
        protected Waitlist<ArgNode<S, A>> waitlist;
        protected StopCriterion<S, A> stopCriterion;
        protected Logger logger;

        protected Builder(final ArgBuilder<S, A, P> argBuilder) {
            this.argBuilder = argBuilder;
            this.projection = s -> 0;
            this.waitlist = FifoWaitlist.create();
            this.stopCriterion = StopCriterions.firstCex();
            this.logger = NullLogger.getInstance();
        }

        public Builder<S, A, P> projection(final Function<? super S, ?> projection) {
            this.projection = projection;
            return this;
        }

        public Builder<S, A, P> waitlist(final Waitlist<ArgNode<S, A>> waitlist) {
            this.waitlist = waitlist;
            return this;
        }

        public Builder<S, A, P> stopCriterion(final StopCriterion<S, A> stopCriterion) {
            this.stopCriterion = stopCriterion;
            return this;
        }

        public Builder<S, A, P> logger(final Logger logger) {
            this.logger = logger;
            return this;
        }

        public BasicArgAbstractor<S, A, P> build() {
            return new BasicArgAbstractor<>(
                    argBuilder, projection, waitlist, stopCriterion, logger);
        }
    }
}
