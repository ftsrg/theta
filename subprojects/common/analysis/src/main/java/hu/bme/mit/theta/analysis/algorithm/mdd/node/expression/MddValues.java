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
package hu.bme.mit.theta.analysis.algorithm.mdd.node.expression;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import hu.bme.mit.delta.java.mdd.MddGraph;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;

/**
 * How the keys of a diagram stand for values and how a step acts on its terminals, attached to the
 * graph. The plain values key literals and leave the terminals alone; {@link SymbolicValues} also
 * key a token whose value a formula in the terminal constrains.
 */
public interface MddValues {

    MddGraph.Key<MddValues> KEY = new MddGraph.Key<>("values");

    MddValues PLAIN = new MddValues() {};

    static MddValues of(MddGraph<?> graph) {
        final MddValues values = graph.getAttribute(KEY);
        return values == null ? PLAIN : values;
    }

    default int toInt(LitExpr<?> literal) {
        return LitExprConverter.toInt(literal);
    }

    default LitExpr<?> toLitExpr(int key, Type type) {
        return LitExprConverter.toLitExpr(key, type);
    }

    /** The value a key of {@code decl} stands for: a literal, or the decl itself for the token. */
    default Expr<?> toExpr(int key, Decl<?> decl) {
        return isToken(key) ? decl.getRef() : toLitExpr(key, decl.getType());
    }

    default boolean isToken(int key) {
        return false;
    }

    /** Whether a step acts on the terminals besides the keys. */
    default boolean actsOnTerminals() {
        return false;
    }

    /** What a terminal says about the values its keys leave open. */
    default Expr<BoolType> formulaOf(MddNode terminal) {
        return True();
    }

    /** The terminal after a step from {@code source} by a relation that ends in {@code step}. */
    default MddNode post(MddNode source, MddNode step, MddGraph<?> graph) {
        return source;
    }

    /**
     * The terminal before a step into {@code target} by a relation that ends in {@code step}, among
     * the states of {@code source}.
     */
    default MddNode pre(MddNode source, MddNode step, MddNode target, MddGraph<?> graph) {
        return target;
    }
}
