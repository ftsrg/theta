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
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.functype.FuncLitExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import java.util.*;
import java.util.stream.Collectors;

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
        final var constToParam = new LinkedHashMap<ConstDecl<?>, ParamDecl<?>>();
        final var aSymbols =
                a.stream()
                        .flatMap(
                                term ->
                                        ExprUtils.getConstants(term).stream()
                                                .map(
                                                        (ConstDecl<?> constDecl) ->
                                                                constToParam
                                                                        .computeIfAbsent(
                                                                                constDecl,
                                                                                it ->
                                                                                        Param(
                                                                                                it
                                                                                                        .getName(),
                                                                                                it
                                                                                                        .getType()))
                                                                        .getRef()))
                        .collect(Collectors.toSet());
        final var bSymbols =
                b.stream()
                        .flatMap(
                                term ->
                                        ExprUtils.getConstants(term).stream()
                                                .map(
                                                        (ConstDecl<?> constDecl) ->
                                                                constToParam
                                                                        .computeIfAbsent(
                                                                                constDecl,
                                                                                it ->
                                                                                        Param(
                                                                                                it
                                                                                                        .getName(),
                                                                                                it
                                                                                                        .getType()))
                                                                        .getRef()))
                        .collect(Collectors.toSet());

        final var commonSymbols = Sets.intersection(aSymbols, bSymbols).toArray(RefExpr[]::new);
        final var aSymbolList = aSymbols.toArray(RefExpr[]::new);
        final var bSymbolList = bSymbols.toArray(RefExpr[]::new);

        Relation A =
                new Relation(
                        "A", Arrays.stream(aSymbolList).map(RefExpr::getType).toArray(Type[]::new));
        Relation B =
                new Relation(
                        "B", Arrays.stream(bSymbolList).map(RefExpr::getType).toArray(Type[]::new));
        Relation itp =
                new Relation(
                        "itp",
                        Arrays.stream(commonSymbols).map(RefExpr::getType).toArray(Type[]::new));

        A.invoke(aSymbolList)
                .plusAssign(a.stream().map(it -> ExprUtils.changeDecls(it, constToParam)).toList());
        B.invoke(bSymbolList)
                .plusAssign(b.stream().map(it -> ExprUtils.changeDecls(it, constToParam)).toList());
        itp.invoke(commonSymbols).plusAssign(A.invoke(aSymbolList).getExpr());
        itp.invoke(commonSymbols).with(B.invoke(bSymbolList).getExpr()).not();

        try (var wpp = new WithPushPop(this)) {
            add(A);
            add(B);
            add(itp);
            var result = check();
            if (result.isSat()) {
                Expr<?> func = getModel().toMap().get(itp.getConstDecl());
                while (func instanceof FuncLitExpr<?, ?> funcLit) {
                    func = funcLit.getResult();
                }
                return (Expr<BoolType>) func;
            } else {
                throw new RuntimeException(
                        "Something went wrong! Interpolation was not successful.");
            }
        } catch (Throwable t) {
            throw new RuntimeException(t);
        }
    }
}
