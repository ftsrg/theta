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
package hu.bme.mit.theta.solver.z3legacy;

import static org.junit.jupiter.api.Assertions.assertEquals;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.fptype.FpExprs;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import java.math.BigInteger;
import org.junit.jupiter.api.Test;

/**
 * The IEEE bit reinterpretation as the z3-legacy backend actually solves it -- the primitive is
 * only useful if Z3 agrees with the constant folder. The oracle is the same JVM encoder used in the
 * core test, but exercised through a real solve rather than {@code eval}.
 */
public class Z3IeeeBvTest {

    private static final FpType DOUBLE = FpType.of(11, 53);

    @Test
    public void fromIeeeBvOfKnownBitsIsTheExpectedDouble() {
        // bits = 0x3FF0000000000000 must force value == 1.0.
        final Solver solver = Z3LegacySolverFactory.getInstance().createSolver();
        final ConstDecl<BvType> bits = Decls.Const("bits", BvType.of(64));
        final BvLitExpr oneBits =
                BvUtils.bigIntegerToUnsignedBvLitExpr(
                        new BigInteger(Long.toUnsignedString(Double.doubleToLongBits(1.0))), 64);
        solver.add(AbstractExprs.Eq(bits.getRef(), oneBits));
        // value != 1.0 while its bits are 1.0's encoding must be UNSAT.
        solver.add(
                BoolExprs.Not(
                        AbstractExprs.Eq(FpExprs.FromIeeeBv(bits.getRef(), DOUBLE), oneDouble())));
        assertEquals(SolverStatus.UNSAT, solver.check());
    }

    @Test
    public void toIeeeBvOfADoubleMatchesTheJvmEncoding() {
        // For a free double f, ToIeeeBv(f) == 0x4009_21FB... (3.14159...) forces f to that value,
        // and then f must not equal a different double.
        final Solver solver = Z3LegacySolverFactory.getInstance().createSolver();
        final ConstDecl<FpType> f = Decls.Const("f", DOUBLE);
        final BvLitExpr piBits =
                BvUtils.bigIntegerToUnsignedBvLitExpr(
                        new BigInteger(
                                Long.toUnsignedString(Double.doubleToLongBits(3.141592653589793))),
                        64);
        solver.add(AbstractExprs.Eq(FpExprs.ToIeeeBv(f.getRef()), piBits));
        // The round trip is forced: reinterpreting those same bits back must equal f. Negation UNSAT.
        solver.add(
                BoolExprs.Not(AbstractExprs.Eq(FpExprs.FromIeeeBv(piBits, DOUBLE), f.getRef())));
        assertEquals(SolverStatus.UNSAT, solver.check());
    }

    @Test
    public void roundTripIsIdentity() {
        // FromIeeeBv(ToIeeeBv(f)) == f for every f: the negation is unsatisfiable.
        final Solver solver = Z3LegacySolverFactory.getInstance().createSolver();
        final ConstDecl<FpType> f = Decls.Const("f", DOUBLE);
        solver.add(
                BoolExprs.Not(
                        AbstractExprs.Eq(
                                FpExprs.FromIeeeBv(FpExprs.ToIeeeBv(f.getRef()), DOUBLE),
                                f.getRef())));
        // NaN != NaN would make this SAT spuriously; exclude NaN, which is the one value that is not
        // its own equal.
        solver.add(BoolExprs.Not(FpExprs.IsNan(f.getRef())));
        assertEquals(SolverStatus.UNSAT, solver.check());
    }

    private hu.bme.mit.theta.core.type.fptype.FpLitExpr oneDouble() {
        return hu.bme.mit.theta.core.utils.FpUtils.bigFloatToFpLitExpr(
                new org.kframework.mpfr.BigFloat(
                        1.0, new org.kframework.mpfr.BinaryMathContext(53, 11)),
                DOUBLE);
    }
}
