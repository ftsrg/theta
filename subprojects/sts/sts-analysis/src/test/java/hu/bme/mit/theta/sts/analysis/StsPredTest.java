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
package hu.bme.mit.theta.sts.analysis;

import static hu.bme.mit.theta.analysis.algorithm.arg.ArgUtils.isWellLabeled;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;
import static org.junit.jupiter.api.Assertions.assertTrue;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.arg.ARG;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgAbstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgCegarChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.BasicArgAbstractor;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.ExprStatePredicate;
import hu.bme.mit.theta.analysis.expr.refinement.*;
import hu.bme.mit.theta.analysis.pred.*;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.Logger.Level;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import hu.bme.mit.theta.sts.STS;
import hu.bme.mit.theta.sts.STS.Builder;
import java.util.function.Predicate;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

public class StsPredTest {

    final Logger logger = new ConsoleLogger(Level.VERBOSE);
    final Solver abstractionSolver = Z3LegacySolverFactory.getInstance().createSolver();
    final ItpSolver refinementSolver = Z3LegacySolverFactory.getInstance().createItpSolver();
    STS sts = null;

    @BeforeEach
    public void setUp() {
        final VarDecl<IntType> vx = Var("x", Int());
        final Expr<IntType> x = vx.getRef();
        final int mod = 3;
        final Builder builder = STS.builder();

        builder.addInit(Eq(x, Int(0)));
        builder.addTrans(
                And(
                        Imply(Lt(x, Int(mod)), Eq(Prime(x), Add(x, Int(1)))),
                        Imply(Geq(x, Int(mod)), Eq(Prime(x), Int(0)))));
        builder.setProp(Not(Eq(x, Int(mod))));

        sts = builder.build();
    }

    @Test
    public void testPredPrec() {

        final Analysis<PredState, ExprAction, PredPrec> analysis =
                PredAnalysis.create(
                        abstractionSolver,
                        PredAbstractors.booleanSplitAbstractor(abstractionSolver),
                        sts.getInit());
        final Predicate<ExprState> target =
                new ExprStatePredicate(Not(sts.getProp()), abstractionSolver);

        final PredPrec prec = PredPrec.of();

        final LTS<State, StsAction> lts = StsLts.create(sts);

        final ArgBuilder<PredState, StsAction, PredPrec> argBuilder =
                ArgBuilder.create(lts, analysis, target);

        final ArgAbstractor<PredState, StsAction, PredPrec> abstractor =
                BasicArgAbstractor.builder(argBuilder).logger(logger).build();

        final ExprTraceChecker<ItpRefutation> exprTraceChecker =
                ExprTraceFwBinItpChecker.create(
                        sts.getInit(), Not(sts.getProp()), refinementSolver);

        final SingleExprTraceRefiner<PredState, StsAction, PredPrec, ItpRefutation> refiner =
                SingleExprTraceRefiner.create(
                        exprTraceChecker,
                        JoiningPrecRefiner.create(new ItpRefToPredPrec(ExprSplitters.atoms())),
                        PruneStrategy.LAZY,
                        logger);

        final SafetyChecker<ARG<PredState, StsAction>, Trace<PredState, StsAction>, PredPrec>
                checker = ArgCegarChecker.create(abstractor, refiner, logger);

        final SafetyResult<ARG<PredState, StsAction>, Trace<PredState, StsAction>> safetyStatus =
                checker.check(prec);
        System.out.println(safetyStatus);

        final ARG<PredState, StsAction> arg = safetyStatus.getProof();
        assertTrue(isWellLabeled(arg, abstractionSolver));

        // System.out.println(new
        // GraphvizWriter().writeString(ArgVisualizer.visualize(arg)));
    }
}
