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
package hu.bme.mit.theta.solver.smtlib.impl.generic;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.HornSolver;
import hu.bme.mit.theta.solver.ProofNode;
import hu.bme.mit.theta.solver.ProofNode.Builder;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibEnumStrategy;
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibSolver;
import hu.bme.mit.theta.solver.smtlib.solver.binary.SmtLibSolverBinary;
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibModel;
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibValuation;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTransformationManager;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Pattern;

/** This solver expects the Horn solver-style proofs for counterexamples */
public class GenericHornSolver extends SmtLibSolver implements HornSolver {
    private static final Pattern CEX_PATTERN =
            Pattern.compile("([0-9]+):\s*(.*)(?=->)->(\s*([0-9]+)(,?\s+[0-9]+)*)?");
    private static final Pattern CEX_ROOT = Pattern.compile("([0-9]+):\s*(.*)");

    private ProofNode proof = null;

    public GenericHornSolver(
            SmtLibSymbolTable symbolTable,
            SmtLibTransformationManager transformationManager,
            SmtLibTermTransformer termTransformer,
            SmtLibSolverBinary solverBinary) {
        super(
                symbolTable,
                transformationManager,
                termTransformer,
                solverBinary,
                false,
                SmtLibEnumStrategy.getDefaultStrategy(),
                "HORN");
    }

    @Override
    public void track(Expr<BoolType> assertion) {
        throw new UnsupportedOperationException("Tracking is not supported by this solver.");
    }

    @Override
    public SolverStatus check() {
        solverBinary.issueCommand("(check-sat)");
        final var response = solverBinary.readResponse().lines().toList();
        status =
                response.get(0).equals("sat")
                        ? SolverStatus.SAT
                        : response.get(0).equals("unsat") ? SolverStatus.UNSAT : null;
        if (status == SolverStatus.SAT) {
            // we have a model
            final var sb = new StringBuilder();
            sb.append("(");
            for (int i = 1; i < response.size(); i++) {
                sb.append(response.get(i)).append("\n");
            }
            sb.append(")");
            final var generalResponse = parseResponse(sb.toString());
            if (generalResponse.isSpecific() && generalResponse.asSpecific().isGetModelResponse()) {
                model =
                        new SmtLibValuation(
                                symbolTable,
                                transformationManager,
                                termTransformer,
                                generalResponse.asSpecific().asGetModelResponse().getModel());
            }
        } else if (status == SolverStatus.UNSAT) {
            // we have a cex (beginning with an empty line)
            final Map<Integer, Builder> builderMap = new LinkedHashMap<>();
            final Map<Builder, List<Integer>> dependencyMap = new LinkedHashMap<>();
            Builder root = null;
            for (int i = 1; i < response.size(); i++) {
                final var matcher = CEX_PATTERN.matcher(response.get(i));
                int idx = -1;
                String term = "";
                List<Integer> dependencies = null;
                if (matcher.matches()) {
                    idx = Integer.parseInt(matcher.group(1));
                    term = matcher.group(2);
                    if (matcher.group(3) != null) {
                        dependencies =
                                Arrays.stream(matcher.group(3).split(",?\s+"))
                                        .filter(it -> !it.isEmpty())
                                        .map(it -> Integer.parseInt(it.trim()))
                                        .toList();
                    } else {
                        dependencies = List.of();
                    }
                } else {
                    final var rootMatcher = CEX_ROOT.matcher(response.get(i));
                    if (rootMatcher.matches()) {
                        idx = Integer.parseInt(rootMatcher.group(1));
                        term = rootMatcher.group(2);
                        dependencies = List.of();
                    }
                }
                if (idx != -1) {
                    final var expr =
                            termTransformer.toExpr(
                                    term, Bool(), new SmtLibModel(Collections.emptyMap()));
                    final var builder = new ProofNode.Builder(expr);
                    if (root == null && expr.equals(False())) {
                        root = builder;
                    }
                    builderMap.put(idx, builder);
                    dependencyMap.put(builder, dependencies);
                }
            }
            dependencyMap.forEach(
                    (builder, integers) ->
                            integers.forEach(integer -> builder.addChild(builderMap.get(integer))));
            proof = root.build();
        }
        return status;
    }

    @Override
    public void push() {
        throw new UnsupportedOperationException("Push is not supported.");
    }

    @Override
    public void pop(int n) {
        throw new UnsupportedOperationException("Pop is not supported.");
    }

    @Override
    public void popAll() {
        throw new UnsupportedOperationException("PopAll is not supported.");
    }

    @Override
    public Collection<Expr<BoolType>> getUnsatCore() {
        throw new UnsupportedOperationException("This solver cannot return unsat cores");
    }

    @Override
    protected void issueGeneralCommand(String command) {
        solverBinary.issueCommand(command);
    }

    @Override
    public ProofNode getProof() {
        checkState(proof != null, "Proof cannot be null! Did you call check()?");
        return proof;
    }

    @Override
    public void clearState() {
        super.clearState();
        proof = null;
    }
}
