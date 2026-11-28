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
package hu.bme.mit.theta.solver.z3;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.BvType;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.Context;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.bvtype.BvEqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvExtractExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public final class Z3TermTransformerTest {

    static {
        Z3SolverFactory.getInstance();
    }

    /** A 24-bit term over an inner extract, large enough for Z3 to print it as a let binding. */
    private static BitVecExpr sharedTermOverExtract(final Context context, final BitVecExpr x) {
        final BitVecExpr low = context.mkExtract(23, 0, x);
        BitVecExpr sum = low;
        for (int i = 0; i < 8; i++) {
            sum = context.mkBVAdd(context.mkBVMul(sum, low), context.mkBV(i, 24));
        }
        return sum;
    }

    @Test
    public void extractOverSharedExtractKeepsItsOwnIndices() {
        try (final Context context = new Context()) {
            final var symbolTable = new Z3SymbolTable();
            final var xDecl = Const("x", BvType(32));
            final var x =
                    (BitVecExpr)
                            new Z3TransformationManager(symbolTable, context)
                                    .toTerm(xDecl.getRef());
            final BitVecExpr inner = sharedTermOverExtract(context, x);
            final var term =
                    context.mkExtract(0, 0, context.mkBVXOR(inner, context.mkBVNot(inner)));
            // The case under test: the inner extract comes first in the term's text.
            Assertions.assertTrue(term.toString().startsWith("(let"), term.toString());

            final Expr<?> expr = new Z3TermTransformer(symbolTable).toExpr(term);

            Assertions.assertEquals(BvType.of(1), expr.getType());
            final var extract = (BvExtractExpr) expr;
            Assertions.assertEquals(IntExprs.Int(0), extract.getFrom());
            Assertions.assertEquals(IntExprs.Int(1), extract.getUntil());
        }
    }

    @Test
    public void bit2boolOverSharedBit2boolKeepsItsOwnIndex() {
        try (final Context context = new Context()) {
            final var symbolTable = new Z3SymbolTable();
            final var xDecl = Const("x", BvType(32));
            final var x = new Z3TransformationManager(symbolTable, context).toTerm(xDecl.getRef());
            String shared = String.format("(ite ((_ bit2bool 3) %1$s) %1$s (bvnot %1$s))", x);
            for (int i = 0; i < 8; i++) {
                shared = String.format("(bvadd (bvmul %s %s) #x0000000%d)", shared, x, i);
            }
            final var term =
                    context.parseSMTLIB2String(
                                    String.format(
                                            "(declare-const %s (_ BitVec 32)) (assert ((_ bit2bool"
                                                    + " 5) (bvxor %2$s (bvnot %2$s))))",
                                            x, shared),
                                    null,
                                    null,
                                    null,
                                    null)[0];
            Assertions.assertTrue(term.toString().startsWith("(let"), term.toString());

            final Expr<?> expr = new Z3TermTransformer(symbolTable).toExpr(term);

            final var extract = (BvExtractExpr) ((BvEqExpr) expr).getLeftOp();
            Assertions.assertEquals(IntExprs.Int(5), extract.getFrom());
            Assertions.assertEquals(IntExprs.Int(6), extract.getUntil());
        }
    }
}
