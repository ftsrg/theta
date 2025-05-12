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

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.utils.ExprUtils.extractFuncAndArgs;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import com.microsoft.z3.Z3Exception;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.functype.FuncAppExpr;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.Map;

public class HornUtils {

    public static ProofNode proofFromExpr(Expr<BoolType> proof) {
        checkState(proof instanceof FuncAppExpr<?, ?>, "Proof must be a function application.");
        int id = 0;
        final Map<Expr<?>, Integer> lookup = new LinkedHashMap<>();

        final var args = extractFuncAndArgs((FuncAppExpr<?, ?>) proof).get2();

        Deque<Expr<?>> proofStack = new LinkedList<>();
        proofStack.push(args.get(0));
        lookup.put(args.get(0), id++);

        Expr<BoolType> root = cast(False(), Bool());
        final var rootBuilder = new ProofNode.Builder(root);

        Map<Integer, ProofNode.Builder> visited = new LinkedHashMap<>();
        visited.put(lookup.get(args.get(0)), rootBuilder);

        while (!proofStack.isEmpty()) {
            final var proofNodeExpr = proofStack.pop();
            if (!visited.containsKey(lookup.getOrDefault(proofNodeExpr, -1))) {
                throw new Z3Exception("Node should exist in the graph nodes");
            }
            final var proofNode = visited.get(lookup.get(proofNodeExpr));

            if (proofNodeExpr instanceof FuncAppExpr<?, ?> funcAppExpr) {
                final var nameAndArgs = extractFuncAndArgs(funcAppExpr);
                if (nameAndArgs.get1() instanceof RefExpr<?> refName
                        && refName.getDecl().getName().startsWith("hyper-res")) {
                    if (!nameAndArgs.get2().isEmpty()) {
                        for (int i = 1; i < nameAndArgs.get2().size() - 1; ++i) {
                            final var child = nameAndArgs.get2().get(i);
                            if (!visited.containsKey(lookup.getOrDefault(child, -1))) {
                                if (!lookup.containsKey(child)) {
                                    lookup.put(child, id++);
                                }
                                visited.put(
                                        lookup.get(child),
                                        new ProofNode.Builder(extractProofExpr(child)));
                                proofStack.push(child);
                            }
                            proofNode.addChild(visited.get(lookup.get(child)));
                        }
                    }
                }
            }
        }
        return rootBuilder.build();
    }

    public static Expr<BoolType> extractProofExpr(Expr<?> expr) {
        checkState(expr instanceof FuncAppExpr<?, ?>, "Proof should be function application.");
        final var nameAndArgs = extractFuncAndArgs((FuncAppExpr<?, ?>) expr);
        final var args = nameAndArgs.get2();
        final var lastArg = args.get(args.size() - 1);
        checkState(lastArg instanceof FuncAppExpr<?, ?>, "Proof should be function application.");
        return (Expr<BoolType>) lastArg;
    }
}
