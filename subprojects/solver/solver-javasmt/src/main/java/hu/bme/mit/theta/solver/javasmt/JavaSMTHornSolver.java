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
package hu.bme.mit.theta.solver.javasmt;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.*;
import java.util.*;
import org.sosy_lab.java_smt.api.*;

final class JavaSMTHornSolver extends JavaSMTSolver implements HornSolver {

    public JavaSMTHornSolver(
            final JavaSMTSymbolTable symbolTable,
            final JavaSMTTransformationManager transformationManager,
            final JavaSMTTermTransformer termTransformer,
            final SolverContext context,
            final BasicProverEnvironment solver) {
        super(symbolTable, transformationManager, termTransformer, context, solver);
    }

    ////

    @Override
    public void track(final Expr<BoolType> assertion) {
        throw new UnsupportedOperationException("Cannot \"track\" in Horn solver");
    }

    @Override
    public Collection<Expr<BoolType>> getUnsatCore() {
        throw new UnsupportedOperationException("Cannot get unsat core in Horn solver");
    }

    private Expr<BoolType> toExpr(Formula f) {
        if (f.toString().matches("query!([0-9]+)")) { // z3 query![0-9]+
            return False();
        }
        final var e = termTransformer.toExpr(f);
        return cast(e, Bool());
    }

    @Override
    public ProofNode getProof() {
        try {
            var proof = solver.getProof();

            var builder = new ProofNode.Builder(toExpr(proof.getFormula()));
            final var rootBuilder = builder;

            proof_transformer:
            while (true) {
                switch (proof.getRule().toString()) {
                    case "ASSERTED":
                        {
                            builder.addChild(new ProofNode.Builder(toExpr(proof.getFormula())));
                            break proof_transformer;
                        }
                    case "HYPER_RESOLVE":
                        {
                            final var childBuilder =
                                    new ProofNode.Builder(toExpr(proof.getFormula()));
                            builder.addChild(childBuilder);
                            if (proof.getChildren().size() > 1) {
                                proof = proof.getChildren().get(1);
                                builder = childBuilder;
                                break;
                            } else {
                                break proof_transformer;
                            }
                        }
                    case "MODUS_PONENS":
                        {
                            final var childBuilder =
                                    new ProofNode.Builder(toExpr(proof.getFormula()));
                            builder.addChild(childBuilder);
                            proof = proof.getChildren().get(0);
                            builder = childBuilder;
                            break;
                        }
                    default:
                        throw new UnsupportedOperationException(
                                "Unsupported proof rule: " + proof.getRule());
                }
            }

            ProofNode ret = rootBuilder.build();
            return ret;

        } catch (SolverException | InterruptedException e) {
            throw new RuntimeException(e);
        }
    }
}
