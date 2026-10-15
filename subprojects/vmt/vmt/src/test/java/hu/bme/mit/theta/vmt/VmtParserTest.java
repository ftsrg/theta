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
package hu.bme.mit.theta.vmt;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;

public class VmtParserTest {

    private SolverContext context;
    private FormulaManager fmgr;

    @BeforeEach
    public void setUp() throws Exception {
        context = SolverContextFactory.createSolverContext(Solvers.Z3);
        fmgr = context.getFormulaManager();
    }

    @AfterEach
    public void tearDown() {
        context.close();
    }

    private boolean equivalent(BooleanFormula a, BooleanFormula b) throws Exception {
        final var bmgr = fmgr.getBooleanFormulaManager();
        try (ProverEnvironment prover = context.newProverEnvironment()) {
            prover.addConstraint(bmgr.not(bmgr.equivalence(a, b)));
            return prover.isUnsat();
        }
    }

    private static final String MODEL =
            """
            ; comment with (unbalanced paren
            (set-logic QF_LIA)
            (declare-fun x () Int)
            (declare-fun |x next| () Int)
            (declare-fun b () Bool)
            (declare-fun b.n () Bool)
            (declare-fun in () Int)
            (define-fun inc ((v Int)) Int (+ v 1))
            (define-fun sv.x () Int (! x :next |x next|))
            (define-fun sv.b () Bool (! b :next b.n))
            (define-fun init () Bool (! (and (= x 0) (! b :named bb)) :init true))
            (define-fun trans () Bool (! (and (= |x next| (inc (+ x in))) (= b.n (not b))) :trans true))
            (define-fun p () Bool (! (>= x 0) :invar-property 0))
            (define-fun q () Bool (! b :live-property 1))
            (assert true)
            (check-sat)
            """;

    @Test
    public void testStructure() throws Exception {
        final VmtModel model = VmtParser.parse(MODEL, fmgr);
        final var imgr = fmgr.getIntegerFormulaManager();
        final var bmgr = fmgr.getBooleanFormulaManager();

        assertEquals(2, model.getStateVars().size());
        final VmtStateVar x = model.getStateVar("x").orElseThrow();
        assertEquals("x next", x.nextName());
        assertEquals(FormulaType.IntegerType, x.type());
        assertEquals(FormulaType.BooleanType, model.getStateVar("b").orElseThrow().type());
        assertEquals(
                List.of(fmgr.makeVariable(FormulaType.IntegerType, "in")), model.getInputVars());

        final var xv = imgr.makeVariable("x");
        final var xn = imgr.makeVariable("x next");
        final var in = imgr.makeVariable("in");
        final var b = bmgr.makeVariable("b");
        final var bn = bmgr.makeVariable("b.n");
        assertTrue(equivalent(model.getInit(), bmgr.and(imgr.equal(xv, imgr.makeNumber(0)), b)));
        assertTrue(
                equivalent(
                        model.getTrans(),
                        bmgr.and(
                                imgr.equal(xn, imgr.add(imgr.add(xv, in), imgr.makeNumber(1))),
                                bmgr.equivalence(bn, bmgr.not(b)))));

        assertEquals(2, model.getProperties().size());
        assertEquals(1, model.getInvariantProperties().size());
        final VmtProperty p = model.getInvariantProperties().get(0);
        assertEquals(0, p.index());
        assertEquals("p", p.name());
        assertTrue(equivalent(p.formula(), imgr.greaterOrEquals(xv, imgr.makeNumber(0))));
        assertEquals(VmtProperty.Kind.LIVENESS, model.getProperties().get(1).kind());
    }

    @Test
    public void testDisjunctiveSplit() {
        final VmtModel model =
                VmtParser.parse(
                        """
                        (declare-fun x () Int)
                        (declare-fun xn () Int)
                        (define-fun .x () Int (! x :next xn))
                        (define-fun .t () Bool (! (or (= xn (+ x 1)) (= xn (- x 1)) (= xn x)) :trans true))
                        """,
                        fmgr);
        assertEquals(3, model.getTransSplit().size());
        assertTrue(fmgr.getBooleanFormulaManager().isTrue(model.getInit()));
        assertTrue(model.getProperties().isEmpty());
    }

    @Test
    public void testErrors() {
        assertThrows(VmtParseException.class, () -> VmtParser.parse("(declare-fun x () Int", fmgr));
        assertThrows(
                VmtParseException.class,
                () -> VmtParser.parse("(declare-fun x () Int)(assert (= x 0))", fmgr));
        assertThrows(
                VmtParseException.class,
                () ->
                        VmtParser.parse(
                                "(declare-fun x () Int)(declare-fun y () Bool)"
                                        + "(define-fun .x () Int (! x :next y))",
                                fmgr));
        assertThrows(
                VmtParseException.class,
                () ->
                        VmtParser.parse(
                                "(declare-fun x () Int)"
                                        + "(define-fun .i () Bool (! (= x undeclared) :init true))",
                                fmgr));
    }

    @Test
    public void testSExprRoundTrip() {
        final List<SExpr> exprs =
                SExprParser.parseAll("(a |b c| \"s \"\" t\" (#b01 -1.5)) ; tail\nfoo");
        assertEquals(2, exprs.size());
        assertEquals("(a |b c| \"s \"\" t\" (#b01 -1.5))", exprs.get(0).toString());
        assertEquals("b c", ((SExpr.Atom) ((SExpr.SList) exprs.get(0)).get(1)).symbolName());
        assertFalse(exprs.get(1) instanceof SExpr.SList);
    }
}
