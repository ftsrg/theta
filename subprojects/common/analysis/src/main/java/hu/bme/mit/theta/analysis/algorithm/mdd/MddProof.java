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
package hu.bme.mit.theta.analysis.algorithm.mdd;

import com.google.common.base.Preconditions;
import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.delta.mdd.MddInterpreter;
import hu.bme.mit.theta.analysis.algorithm.InvariantProof;
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.MddExpressionRepresentation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public class MddProof implements InvariantProof {

    private final MddHandle stateSpace;
    private final MddExpressionRepresentation.MddToExprStrategy toExprStrategy;
    private Long size = null;
    private Expr<BoolType> invariant = null;

    private MddProof(
            MddHandle stateSpace,
            MddExpressionRepresentation.MddToExprStrategy toExprStrategy) {
        Preconditions.checkArgument(toExprStrategy != MddExpressionRepresentation.MddToExprStrategy.NONE && toExprStrategy != MddExpressionRepresentation.MddToExprStrategy.VARIABLE_LEVEL, "Must use a strategy that provides a precise invariant.");
        this.stateSpace = stateSpace;
        this.toExprStrategy = toExprStrategy;
    }

    public static MddProof of(MddHandle stateSpace) {
        return new MddProof(
                stateSpace, MddExpressionRepresentation.MddToExprStrategy.VECTOR_LEVEL);
    }

    public static MddProof of(
            MddHandle stateSpace,
            MddExpressionRepresentation.MddToExprStrategy toExprStrategy) {
        return new MddProof(stateSpace, toExprStrategy);
    }

    public Long size() {
        if (size == null) {
            size = MddInterpreter.calculateNonzeroCount(stateSpace);
        }
        return size;
    }

    public MddHandle getMdd() {
        return stateSpace;
    }

    @Override
    public Expr<BoolType> getInvariant() {
        if (invariant == null) {
            invariant = toExprStrategy.toExpr(stateSpace);
        }
        return invariant;
    }
}
