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

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static hu.bme.mit.theta.solver.HornUtils.proofFromExpr;

import com.google.common.collect.Lists;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.solver.HornSolver;
import hu.bme.mit.theta.solver.ProofNode;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.SortContext;
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibEnumStrategy;
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibSolver;
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibSolverException;
import hu.bme.mit.theta.solver.smtlib.solver.binary.SmtLibSolverBinary;
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibModel;
import hu.bme.mit.theta.solver.smtlib.solver.parser.GetProofResponse;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTransformationManager;
import java.util.*;

/**
 * This class is a HornSolver that expects the proofs to be in the style of Z3 (using hyper-res
 * predicates)
 */
public class GenericSmtLibHornSolver extends SmtLibSolver implements HornSolver {

    public GenericSmtLibHornSolver(
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

    public static Type transformSort(final SortContext ctx) {
        final String name = ctx.identifier().symbol().getText();
        return switch (name) {
            case "Int" -> Int();
            case "Bool" -> Bool();
            case "Real" -> Rat();
            case "BitVec" -> {
                assert ctx.identifier().index().size() == 1;
                yield BvExprs.BvType(Integer.parseInt(ctx.identifier().index().get(0).getText()));
            }
            case "Array" -> {
                assert ctx.sort().size() == 2;
                yield Array(transformSort(ctx.sort().get(0)), transformSort(ctx.sort().get(1)));
            }
            default -> throw new UnsupportedOperationException();
        };
    }

    @Override
    public ProofNode getProof() {
        solverBinary.issueCommand("(get-proof)");
        var response = solverBinary.readResponse();
        final var res = parseResponse(response);
        if (res.isError()) {
            throw new SmtLibSolverException(res.getReason());
        } else if (res.isSpecific()) {
            final GetProofResponse getModelResponse = res.asSpecific().asGetProofResponse();
            getModelResponse
                    .getFunDeclarations()
                    .forEach(
                            (name, def) -> {
                                var type = transformSort(def.get2());
                                for (SortContext s : Lists.reverse(def.get1())) {
                                    type = FuncType.of(transformSort(s), type);
                                }
                                symbolTable.put(Const(name, type), name, def.get3());
                            });
            final var proof =
                    termTransformer.toExpr(
                            getModelResponse.getProof(),
                            Bool(),
                            new SmtLibModel(Collections.emptyMap()));
            return proofFromExpr(proof);
        } else {
            throw new AssertionError();
        }
    }
}
