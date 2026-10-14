/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.vmt.analysis.mdd;

import com.google.common.base.Preconditions;
import com.koloboke.collect.map.ObjObjMap;
import com.koloboke.collect.map.hash.HashObjObjMaps;
import hu.bme.mit.delta.collections.IntStatistics;
import hu.bme.mit.delta.java.mdd.BinaryOperationCache;
import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddVariable;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

/**
 * The JavaSMT counterpart of {@code MddToExprVariableLevel}: over-approximates an MDD by the bounds
 * of each integer variable, which guides the enumeration of a constrained cursor.
 */
public final class FormulaBoundsConstraint {

    private FormulaBoundsConstraint() {}

    public static BooleanFormula of(MddHandle mddHandle, FormulaMddContext ctx) {
        final var bounds =
                BoundsCollector.traverse(
                        mddHandle.getNode(),
                        mddHandle.getVariableHandle().getVariable().orElseThrow());
        final IntegerFormulaManager imgr = ctx.getFormulaManager().getIntegerFormulaManager();
        final List<BooleanFormula> constraints = new ArrayList<>();
        for (var entry : bounds.entrySet()) {
            final FormulaVar var = (FormulaVar) entry.getKey().getTraceInfo();
            final BoundsCollector.Bounds boundsForVar = entry.getValue();
            if (!boundsForVar.hasDefault && var.type().isIntegerType()) {
                final IntegerFormula formula = (IntegerFormula) var.formula();
                final IntegerFormula lower =
                        imgr.makeNumber(BigInteger.valueOf(boundsForVar.lower));
                if (boundsForVar.lower == boundsForVar.upper) {
                    constraints.add(imgr.equal(formula, lower));
                } else {
                    constraints.add(imgr.greaterOrEquals(formula, lower));
                    constraints.add(
                            imgr.lessOrEquals(
                                    formula,
                                    imgr.makeNumber(BigInteger.valueOf(boundsForVar.upper))));
                }
            }
        }
        return ctx.getBooleanFormulaManager().and(constraints);
    }

    private static class BoundsCollector {

        static class Bounds {
            int lower;
            int upper;
            boolean hasDefault;

            Bounds(int lower, int upper, boolean hasDefault) {
                this.lower = lower;
                this.upper = upper;
                this.hasDefault = hasDefault;
            }
        }

        private static final BinaryOperationCache<
                        MddNode, MddVariable, ObjObjMap<MddVariable, Bounds>>
                cache = new BinaryOperationCache<>();

        static ObjObjMap<MddVariable, Bounds> traverse(
                final MddNode node, final MddVariable variable) {
            final var cached = cache.getOrNull(node, variable);
            if (cached != null) {
                return cached;
            }
            if (node.isTerminal()) {
                return HashObjObjMaps.newUpdatableMap();
            }

            Preconditions.checkNotNull(variable);

            for (var c = node.cursor();
                    c.moveNext(); ) {} // explores the node fully before reading its bounds

            final ObjObjMap<MddVariable, Bounds> returnValue = HashObjObjMaps.newUpdatableMap();
            final var currentBounds = new Bounds(Integer.MAX_VALUE, Integer.MIN_VALUE, false);

            final List<ObjObjMap<MddVariable, Bounds>> childBounds = new ArrayList<>();

            final var nodeInterpreter = variable.getNodeInterpreter(node);
            if (nodeInterpreter.defaultValue() != null) {
                final MddNode defaultValue = nodeInterpreter.defaultValue();
                childBounds.add(traverse(defaultValue, variable.getLower().orElse(null)));
                currentBounds.hasDefault = true;
            } else {
                final IntStatistics statistics = nodeInterpreter.statistics();
                currentBounds.lower = statistics.lowestValue();
                currentBounds.upper = statistics.highestValue();

                for (var cur = nodeInterpreter.cursor(); cur.moveNext(); ) {
                    if (cur.value() != null) {
                        childBounds.add(traverse(cur.value(), variable.getLower().orElse(null)));
                    }
                }
            }

            returnValue.put(variable, currentBounds);
            for (final var childBoundMap : childBounds) {
                for (final var entry : childBoundMap.entrySet()) {
                    final MddVariable var = entry.getKey();
                    final Bounds childBoundsForVar = entry.getValue();

                    final Bounds existingBounds = returnValue.getOrDefault(var, null);
                    if (existingBounds == null) {
                        returnValue.put(
                                var,
                                new Bounds(
                                        childBoundsForVar.lower,
                                        childBoundsForVar.upper,
                                        childBoundsForVar.hasDefault));
                    } else {
                        existingBounds.lower =
                                Math.min(existingBounds.lower, childBoundsForVar.lower);
                        existingBounds.upper =
                                Math.max(existingBounds.upper, childBoundsForVar.upper);
                        existingBounds.hasDefault |= childBoundsForVar.hasDefault;
                    }
                }
            }
            cache.addToCache(node, variable, returnValue);
            return returnValue;
        }
    }
}
