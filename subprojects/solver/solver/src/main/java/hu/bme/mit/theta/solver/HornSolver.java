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
package hu.bme.mit.theta.solver;

import static hu.bme.mit.theta.core.decl.Decls.Param;

import com.google.common.collect.Sets;
import hu.bme.mit.theta.core.Relation;
import hu.bme.mit.theta.core.Rule;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.functype.FuncLitExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import java.util.*;
import java.util.stream.Collectors;
import kotlin.Pair;

/** The HornSolver can provide proofs, and accept Relations */
public interface HornSolver extends Solver {

    default void add(Relation relation) {
        add(relation.getRules().stream().map(Rule::toExpr).toList());
    }

    default void add(Collection<? extends Relation> relations) {
        add(relations.stream().flatMap(it -> it.getRules().stream().map(Rule::toExpr)).toList());
    }

    /** Get the proof found in the solver. */
    default ProofNode getProof() {
        throw new UnsupportedOperationException("Cannot get proof.");
    }

    default Expr<BoolType> interpolate(List<Expr<BoolType>> a, List<Expr<BoolType>> b) {
        final var aConstants = ExprUtils.getConstants(a);
        final var bConstants = ExprUtils.getConstants(b);
        final var commonConstants = Sets.intersection(aConstants, bConstants).stream().toList();

        final var constToParam =
                Sets.union(aConstants, bConstants).stream()
                        .map(it -> new Pair<>(it, Param(it.getName(), it.getType())))
                        .collect(Collectors.toMap(Pair::getFirst, Pair::getSecond));

        final var aParamArr = aConstants.stream().map(constToParam::get).toArray(ParamDecl[]::new);
        final var bParamArr = bConstants.stream().map(constToParam::get).toArray(ParamDecl[]::new);
        final var commonParamArr =
                commonConstants.stream().map(constToParam::get).toArray(ParamDecl[]::new);

        final var aRefArr = Arrays.stream(aParamArr).map(Decl::getRef).toArray(RefExpr[]::new);
        final var bRefArr = Arrays.stream(bParamArr).map(Decl::getRef).toArray(RefExpr[]::new);
        final var commonRefArr =
                Arrays.stream(commonParamArr).map(Decl::getRef).toArray(RefExpr[]::new);

        final var aTypeArr = Arrays.stream(aParamArr).map(Decl::getType).toArray(Type[]::new);
        final var bTypeArr = Arrays.stream(bParamArr).map(Decl::getType).toArray(Type[]::new);
        final var commonTypeArr =
                Arrays.stream(commonParamArr).map(Decl::getType).toArray(Type[]::new);

        Relation A = new Relation("A", aTypeArr);
        Relation B = new Relation("B", bTypeArr);
        Relation itp = new Relation("itp", commonTypeArr);

        A.invoke(aRefArr)
                .plusAssign(a.stream().map(it -> ExprUtils.changeDecls(it, constToParam)).toList());
        B.invoke(bRefArr)
                .plusAssign(b.stream().map(it -> ExprUtils.changeDecls(it, constToParam)).toList());
        itp.invoke(commonRefArr).plusAssign(A.invoke(aRefArr).getExpr());
        itp.invoke(commonRefArr).with(B.invoke(bRefArr).getExpr()).not();

        add(A);
        add(B);
        add(itp);
        var result = check();
        if (result.isSat()) {
            Expr<?> func = getModel().toMap().get(itp.getConstDecl());
            final var revMap = new LinkedHashMap<Decl<?>, Decl<?>>();
            int i = 0;
            while (func instanceof FuncLitExpr<?, ?> funcLit) {
                revMap.put(((FuncLitExpr<?, ?>) func).getParam(), commonConstants.get(i++));
                func = funcLit.getResult();
            }
            return (Expr<BoolType>) ExprUtils.changeDecls(func, revMap);
        } else {
            throw new RuntimeException("Something went wrong! Interpolation was not successful.");
        }
    }
}
