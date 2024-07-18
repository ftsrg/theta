/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.expr.refinement;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.arg.ARG;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgRefiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.RefinerResult;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.decl.VarDecl;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

public final class AasporRefiner<S extends ExprState, A extends ExprAction, P extends Prec> implements ArgRefiner<S, A, P> {

    private final ArgRefiner<S, A, P> refiner;

    private final PruneStrategy pruneStrategy;

    private final Map<VarDecl<?>, Set<S>> ignoredVarRegistry;

    private AasporRefiner(final ArgRefiner<S, A, P> refiner,
                          final PruneStrategy pruneStrategy,
                          final Map<VarDecl<?>, Set<S>> ignoredVarRegistry) {
        this.refiner = refiner;
        this.pruneStrategy = pruneStrategy;
        this.ignoredVarRegistry = ignoredVarRegistry;
    }

    public static <S extends ExprState, A extends ExprAction, P extends Prec> AasporRefiner<S, A, P> create(
            final ArgRefiner<S, A, P> refiner, final PruneStrategy pruneStrategy,
            final Map<VarDecl<?>, Set<S>> ignoredVarRegistry) {
        return new AasporRefiner<>(refiner, pruneStrategy, ignoredVarRegistry);
    }

    @Override
    public RefinerResult<S, A, P, Trace<S, A>> refine(final ARG<S, A> arg, final P prec) {
        final RefinerResult<S, A, P, Trace<S, A>> result = refiner.refine(arg, prec);
        if (result.isUnsafe() || pruneStrategy != PruneStrategy.LAZY) return result;

        final P newPrec = result.asSpurious().getRefinedPrec();
        final Set<VarDecl<?>> newlyAddedVars = new HashSet<>(newPrec.getUsedVars());
        newlyAddedVars.removeAll(prec.getUsedVars());

        newlyAddedVars.forEach(newVar -> {
            if (ignoredVarRegistry.containsKey(newVar)) {
                Set<ArgNode<S, A>> nodesToReExpand = ignoredVarRegistry.get(newVar).stream().flatMap(stateToPrune ->
                        arg.getNodes().filter(node -> node.getState().equals(stateToPrune)) // TODO one state can be in one ARG node?
                ).collect(Collectors.toSet());
                nodesToReExpand.forEach(arg::markForReExpansion);
                ignoredVarRegistry.remove(newVar);
            }
        });

        return result;
    }
}
