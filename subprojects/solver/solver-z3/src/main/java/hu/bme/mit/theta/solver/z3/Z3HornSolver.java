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
package hu.bme.mit.theta.solver.z3;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.UnsafeApp;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Z3Exception;
import com.microsoft.z3.enumerations.Z3_decl_kind;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.solver.HornSolver;
import hu.bme.mit.theta.solver.ProofNode;
import hu.bme.mit.theta.solver.ProofNode.Builder;
import hu.bme.mit.theta.solver.SolverStatus;
import java.util.Arrays;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

final class Z3HornSolver extends Z3Solver implements HornSolver {
    public Z3HornSolver(
            Z3SymbolTable symbolTable,
            Z3TransformationManager transformationManager,
            Z3TermTransformer termTransformer,
            Context z3Context,
            Solver z3Solver) {
        super(symbolTable, transformationManager, termTransformer, z3Context, z3Solver);
    }

    ////

    private Expr<BoolType> toProofExpr(com.microsoft.z3.Expr<?> expr) {
        final var args = expr.getArgs();
        final var lastArg = args[args.length - 1];
        checkState(lastArg.isApp());
        final var name = lastArg.getFuncDecl().getName().toString();
        final var params = lastArg.getArgs();
        final var paramValues = Arrays.stream(params).map(termTransformer::toExpr).toList();
        final List<Type> paramTypes =
                paramValues.stream().map(expr1 -> (Type) expr1.getType()).toList();

        final var funcType =
                paramTypes.stream().reduce(Bool(), (res, param) -> FuncType.of(param, res));
        final var decl = Const(name, funcType);
        Expr<?> func = decl.getRef();
        for (Expr<?> paramValue : paramValues) {
            func = UnsafeApp(func, paramValue);
        }
        return (Expr<BoolType>) func;
    }

    /**
     * This is a best-effort solution, hopefully would support (most) CHCs at least. Taken from
     * https://github.com/ethereum/solidity/blob/5917fd82b3ca4cab5f817f78b8da8ebe409dd02e/libsmtutil/Z3CHCInterface.cpp#L130
     * and adapted to the Java API.
     */
    @Override
    public ProofNode getProof() {
        checkState(status == SolverStatus.UNSAT, "Cannot get proof if status is not UNSAT");
        com.microsoft.z3.Expr<?> proof = z3Solver.getProof();

        Deque<com.microsoft.z3.Expr<?>> proofStack = new LinkedList<>();
        proofStack.push(proof.getArgs()[0]);

        Expr<BoolType> root = cast(False(), Bool());
        final var rootBuilder = new ProofNode.Builder(root);

        Map<Integer, ProofNode.Builder> visited = new LinkedHashMap<>();
        visited.put(proofStack.peek().getId(), rootBuilder);

        while (!proofStack.isEmpty()) {
            final var proofNodeExpr = proofStack.pop();
            if (!visited.containsKey(proofNodeExpr.getId())) {
                throw new Z3Exception("Node should exist in the graph nodes");
            }
            final var proofNode = visited.get(proofNodeExpr.getId());

            if (proofNodeExpr.isApp()
                    && proofNodeExpr.getFuncDecl().getDeclKind()
                            == Z3_decl_kind.Z3_OP_PR_HYPER_RESOLVE) {
                if (proofNodeExpr.getArgs().length > 0) {
                    for (int i = 1; i < proofNodeExpr.getArgs().length - 1; ++i) {
                        final var child = proofNodeExpr.getArgs()[i];
                        if (!visited.containsKey(child.getId())) {
                            visited.put(child.getId(), new Builder(toProofExpr(child)));
                            proofStack.push(child);
                        }
                        proofNode.addChild(visited.get(child.getId()));
                    }
                }
            }
        }

        return rootBuilder.build();
    }
}
