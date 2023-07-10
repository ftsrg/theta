/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.expr.refinement.autoexpl;

import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.BinaryExpr;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;

import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

public class NewOperandsAutoExpl implements AutoExpl {

    private final Set<VarDecl<?>> explVars = Containers.createSet();
    private final Map<Decl<?>, Set<Expr<?>>> modelOperands;
    private final Map<Decl<?>, Set<Expr<?>>> newOperands;
    private final int newOperandsLimit;

    public NewOperandsAutoExpl(final Set<VarDecl<?>> explPreferredVars,
                               final Map<Decl<?>, Set<Expr<?>>> modelOperands, final int newOperandsLimit) {
        explVars.addAll(explPreferredVars);
        this.newOperandsLimit = newOperandsLimit;
        this.modelOperands = modelOperands;

        this.newOperands = Containers.createMap();
    }

    @Override
    public boolean isExpl(VarDecl<?> decl) {
        return explVars.contains(decl);
    }

    @Override
    public void update(Expr<BoolType> itp) {

        final Set<Expr<BoolType>> canonicalAtoms = ExprUtils.getAtoms(itp).stream()
                .map(ExprUtils::canonize)
                .flatMap(atom -> ExprUtils.getAtoms(atom).stream())
                .collect(Collectors.toSet());
        canonicalAtoms.stream()
                .filter(atom -> atom.getOps().size() > 1)
                .forEach(
                        atom -> {
                            atom.getOps().stream()
                                    .filter(RefExpr.class::isInstance)
                                    .map(RefExpr.class::cast)
                                    .forEach(
                                            ref -> atom.getOps().stream()
                                                    .filter(Predicate.not(ref::equals))
                                                    .forEach(
                                                            op -> {
                                                                final Decl<?> decl = ref.getDecl();
                                                                if (modelOperands.containsKey(decl) && !modelOperands.get(
                                                                        decl).contains(op)) {
                                                                    newOperands.computeIfAbsent(decl,
                                                                            k -> Containers.createSet()).add(op);
                                                                }
                                                            }
                                                    )

                                    );
                        }
                );

        explVars.addAll(
                ExprUtils.getVars(itp).stream()
                        .filter(decl ->
                                newOperands.containsKey(decl) && newOperands.get(decl).size() > newOperandsLimit
                                        || decl.getType() == Bool())
                        .collect(Collectors.toSet()));

    }
}
