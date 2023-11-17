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
package hu.bme.mit.theta.xsts.analysis;

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.kind.KIndChecker;
import hu.bme.mit.theta.analysis.algorithm.kind.KIndChecker2;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.Logger.Level;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.Stmts;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.StmtUnfoldResult;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfig;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder;
import hu.bme.mit.theta.xsts.dsl.XstsDslManager;
import org.checkerframework.checker.units.qual.A;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.SequenceInputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
import static org.junit.Assert.assertTrue;

@RunWith(value = Parameterized.class)
public class XstsTest {

    @Parameterized.Parameter(value = 0)
    public String filePath;

    @Parameterized.Parameter(value = 1)
    public String propPath;

    @Parameterized.Parameter(value = 2)
    public boolean safe;

    @Parameterized.Parameter(value = 3)
    public XstsConfigBuilder.Domain domain;

    @Parameterized.Parameters(name = "{index}: {0}, {1}, {2}, {3}")
    public static Collection<Object[]> data() {
        return Arrays.asList(new Object[][]{

                {"src/test/resources/model/trafficlight.xsts",
                        "src/test/resources/property/green_and_red.prop", true,
                        XstsConfigBuilder.Domain.EXPL},

                {"src/test/resources/model/trafficlight.xsts",
                        "src/test/resources/property/green_and_red.prop", true,
                        XstsConfigBuilder.Domain.PRED_CART},

                {"src/test/resources/model/trafficlight.xsts",
                        "src/test/resources/property/green_and_red.prop", true,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                {"src/test/resources/model/trafficlight_v2.xsts",
                        "src/test/resources/property/green_and_red.prop", true,
                        XstsConfigBuilder.Domain.EXPL},

                {"src/test/resources/model/trafficlight_v2.xsts",
                        "src/test/resources/property/green_and_red.prop", true,
                        XstsConfigBuilder.Domain.PRED_CART},

                {"src/test/resources/model/trafficlight_v2.xsts",
                        "src/test/resources/property/green_and_red.prop", true,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                {"src/test/resources/model/counter5.xsts",
                        "src/test/resources/property/x_between_0_and_5.prop", true,
                        XstsConfigBuilder.Domain.EXPL},

                {"src/test/resources/model/counter5.xsts",
                        "src/test/resources/property/x_between_0_and_5.prop", true,
                        XstsConfigBuilder.Domain.PRED_CART},

<<<<<<< HEAD
                {"src/test/resources/model/counter5.xsts",
                        "src/test/resources/property/x_between_0_and_5.prop", true,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},
=======

>>>>>>> 727693816 (loopcheck fixed, xsts input fixed)

                {"src/test/resources/model/counter5.xsts", "src/test/resources/property/x_eq_5.prop",
                        false, XstsConfigBuilder.Domain.EXPL},

                {"src/test/resources/model/counter5.xsts", "src/test/resources/property/x_eq_5.prop",
                        false, XstsConfigBuilder.Domain.PRED_CART},

                {"src/test/resources/model/counter5.xsts", "src/test/resources/property/x_eq_5.prop",
                        false, XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                {"src/test/resources/model/x_and_y.xsts", "src/test/resources/property/x_geq_y.prop",
                        true, XstsConfigBuilder.Domain.PRED_CART},

                {"src/test/resources/model/x_powers.xsts", "src/test/resources/property/x_even.prop",
                        true, XstsConfigBuilder.Domain.PRED_CART},

                {"src/test/resources/model/cross_with.xsts", "src/test/resources/property/cross.prop",
                        false, XstsConfigBuilder.Domain.PRED_CART},

//                { "src/test/resources/model/cross_with.xsts", "src/test/resources/property/cross.prop", false, XstsConfigBuilder.Domain.EXPL},

//                { "src/test/resources/model/cross_with.xsts", "src/test/resources/property/cross.prop", false, XstsConfigBuilder.Domain.PROD},

                {"src/test/resources/model/cross_without.xsts",
                        "src/test/resources/property/cross.prop", false,
                        XstsConfigBuilder.Domain.PRED_CART},

//                { "src/test/resources/model/cross_without.xsts", "src/test/resources/property/cross.prop", false, XstsConfigBuilder.Domain.EXPL},

//                { "src/test/resources/model/cross_without.xsts", "src/test/resources/property/cross.prop", false, XstsConfigBuilder.Domain.PROD},

                {"src/test/resources/model/choices.xsts", "src/test/resources/property/choices.prop",
                        false, XstsConfigBuilder.Domain.PRED_CART},

                {"src/test/resources/model/choices.xsts", "src/test/resources/property/choices.prop",
                        false, XstsConfigBuilder.Domain.EXPL},

                {"src/test/resources/model/choices.xsts", "src/test/resources/property/choices.prop",
                        false, XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                {"src/test/resources/model/literals.xsts", "src/test/resources/property/literals.prop",
                        true, XstsConfigBuilder.Domain.PRED_CART},

                {"src/test/resources/model/literals.xsts", "src/test/resources/property/literals.prop",
                        true, XstsConfigBuilder.Domain.EXPL},

                {"src/test/resources/model/literals.xsts", "src/test/resources/property/literals.prop",
                        true, XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                {"src/test/resources/model/cross3.xsts", "src/test/resources/property/cross.prop",
                        false, XstsConfigBuilder.Domain.PRED_CART},

//                { "src/test/resources/model/cross3.xsts", "src/test/resources/property/cross.prop", false, XstsConfigBuilder.Domain.EXPL},

//                { "src/test/resources/model/cross3.xsts", "src/test/resources/property/cross.prop", false, XstsConfigBuilder.Domain.PROD},

                {"src/test/resources/model/sequential.xsts",
                        "src/test/resources/property/sequential.prop", true,
                        XstsConfigBuilder.Domain.PRED_CART},

                {"src/test/resources/model/sequential.xsts",
                        "src/test/resources/property/sequential.prop", true, XstsConfigBuilder.Domain.EXPL},

                {"src/test/resources/model/sequential.xsts",
                        "src/test/resources/property/sequential.prop", true,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                {"src/test/resources/model/sequential.xsts",
                        "src/test/resources/property/sequential2.prop", false,
                        XstsConfigBuilder.Domain.PRED_CART},

                {"src/test/resources/model/sequential.xsts",
                        "src/test/resources/property/sequential2.prop", false,
                        XstsConfigBuilder.Domain.EXPL},

                {"src/test/resources/model/sequential.xsts",
                        "src/test/resources/property/sequential2.prop", false,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                {"src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine.prop", false,
                        XstsConfigBuilder.Domain.PRED_CART},

                {"src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine.prop", false,
                        XstsConfigBuilder.Domain.EXPL},

                {"src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine.prop", false,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                {"src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine2.prop", true,
                        XstsConfigBuilder.Domain.PRED_CART},

                {"src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine2.prop", true,
                        XstsConfigBuilder.Domain.EXPL},

                {"src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine2.prop", true,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                {"src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine3.prop", false,
                        XstsConfigBuilder.Domain.PRED_CART},

                {"src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine3.prop", false,
                        XstsConfigBuilder.Domain.EXPL},

                {"src/test/resources/model/on_off_statemachine.xsts",
                        "src/test/resources/property/on_off_statemachine3.prop", false,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                {"src/test/resources/model/counter50.xsts", "src/test/resources/property/x_eq_5.prop",
                        false, XstsConfigBuilder.Domain.PRED_CART},

                {"src/test/resources/model/counter50.xsts", "src/test/resources/property/x_eq_5.prop",
                        false, XstsConfigBuilder.Domain.EXPL},

                {"src/test/resources/model/counter50.xsts", "src/test/resources/property/x_eq_5.prop",
                        false, XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

//                { "src/test/resources/model/counter50.xsts", "src/test/resources/property/x_eq_50.prop", false, XstsConfigBuilder.Domain.PRED_CART},

                {"src/test/resources/model/counter50.xsts", "src/test/resources/property/x_eq_50.prop",
                        false, XstsConfigBuilder.Domain.EXPL},

                {"src/test/resources/model/counter50.xsts", "src/test/resources/property/x_eq_50.prop",
                        false, XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                {"src/test/resources/model/counter50.xsts", "src/test/resources/property/x_eq_51.prop",
                        true, XstsConfigBuilder.Domain.PRED_CART},

                {"src/test/resources/model/counter50.xsts", "src/test/resources/property/x_eq_51.prop",
                        true, XstsConfigBuilder.Domain.EXPL},

                {"src/test/resources/model/counter50.xsts", "src/test/resources/property/x_eq_51.prop",
                        true, XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                {"src/test/resources/model/count_up_down.xsts",
                        "src/test/resources/property/count_up_down.prop", false,
                        XstsConfigBuilder.Domain.PRED_CART},

                {"src/test/resources/model/count_up_down.xsts",
                        "src/test/resources/property/count_up_down.prop", false,
                        XstsConfigBuilder.Domain.EXPL},

                {"src/test/resources/model/count_up_down.xsts",
                        "src/test/resources/property/count_up_down.prop", false,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                {"src/test/resources/model/count_up_down.xsts",
                        "src/test/resources/property/count_up_down2.prop", true,
                        XstsConfigBuilder.Domain.PRED_CART},

                {"src/test/resources/model/count_up_down.xsts",
                        "src/test/resources/property/count_up_down2.prop", true,
                        XstsConfigBuilder.Domain.EXPL},

<<<<<<< HEAD
                {"src/test/resources/model/count_up_down.xsts",
                        "src/test/resources/property/count_up_down2.prop", true,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},
=======

>>>>>>> 727693816 (loopcheck fixed, xsts input fixed)

                {"src/test/resources/model/bhmr2007.xsts", "src/test/resources/property/bhmr2007.prop",
                        true, XstsConfigBuilder.Domain.PRED_CART},

//                { "src/test/resources/model/bhmr2007.xsts", "src/test/resources/property/bhmr2007.prop", true, XstsConfigBuilder.Domain.EXPL},

//                { "src/test/resources/model/bhmr2007.xsts", "src/test/resources/property/bhmr2007.prop", true, XstsConfigBuilder.Domain.PROD},

                {"src/test/resources/model/css2003.xsts", "src/test/resources/property/css2003.prop",
                        true, XstsConfigBuilder.Domain.PRED_CART},

                {"src/test/resources/model/css2003.xsts", "src/test/resources/property/css2003.prop",
                        true, XstsConfigBuilder.Domain.EXPL},

                {"src/test/resources/model/css2003.xsts", "src/test/resources/property/css2003.prop",
                        true, XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

//                { "src/test/resources/model/ort.xsts", "src/test/resources/property/x_gt_2.prop", false, XstsConfigBuilder.Domain.PRED_CART},

//                { "src/test/resources/model/ort2.xsts", "src/test/resources/property/ort2.prop", true, XstsConfigBuilder.Domain.PRED_CART},

//                { "src/test/resources/model/crossroad_composite.xsts", "src/test/resources/property/both_green.prop", true, XstsConfigBuilder.Domain.EXPL}

                {"src/test/resources/model/array_counter.xsts",
                        "src/test/resources/property/array_10.prop", false,
                        XstsConfigBuilder.Domain.PRED_CART},

                {"src/test/resources/model/array_counter.xsts",
                        "src/test/resources/property/array_10.prop", false, XstsConfigBuilder.Domain.EXPL},

                {"src/test/resources/model/array_counter.xsts",
                        "src/test/resources/property/array_10.prop", false,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                {"src/test/resources/model/array_constant.xsts",
                        "src/test/resources/property/array_constant.prop", true,
                        XstsConfigBuilder.Domain.PRED_CART},

                {"src/test/resources/model/array_constant.xsts",
                        "src/test/resources/property/array_constant.prop", true,
                        XstsConfigBuilder.Domain.EXPL},

                {"src/test/resources/model/array_constant.xsts",
                        "src/test/resources/property/array_constant.prop", true,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                {"src/test/resources/model/localvars.xsts",
                        "src/test/resources/property/localvars.prop", true,
                        XstsConfigBuilder.Domain.PRED_CART},

                {"src/test/resources/model/localvars.xsts",
                        "src/test/resources/property/localvars.prop", true, XstsConfigBuilder.Domain.EXPL},

                {"src/test/resources/model/localvars.xsts",
                        "src/test/resources/property/localvars.prop", true,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                {"src/test/resources/model/localvars2.xsts",
                        "src/test/resources/property/localvars2.prop", true,
                        XstsConfigBuilder.Domain.PRED_CART},

                {"src/test/resources/model/localvars2.xsts",
                        "src/test/resources/property/localvars2.prop", true, XstsConfigBuilder.Domain.EXPL},

                {"src/test/resources/model/localvars2.xsts",
                        "src/test/resources/property/localvars2.prop", true,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                {"src/test/resources/model/loopxy.xsts", "src/test/resources/property/loopxy.prop",
                        true, XstsConfigBuilder.Domain.EXPL},

                {"src/test/resources/model/loopxy.xsts", "src/test/resources/property/loopxy.prop",
                        true, XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                {"src/test/resources/model/loopxy.xsts", "src/test/resources/property/loopxy.prop",
                        true, XstsConfigBuilder.Domain.PRED_CART},

                {"src/test/resources/model/arraywrite_sugar.xsts",
                        "src/test/resources/property/arraywrite_sugar.prop", false,
                        XstsConfigBuilder.Domain.PRED_CART},

                {"src/test/resources/model/if1.xsts", "src/test/resources/property/if1.prop", true,
                        XstsConfigBuilder.Domain.PRED_CART},

                {"src/test/resources/model/if2.xsts", "src/test/resources/property/if2.prop", false,
                        XstsConfigBuilder.Domain.EXPL_PRED_COMBINED}
        });
    }

    @Test
    public void test() throws IOException {

        final Logger logger = new ConsoleLogger(Level.SUBSTEP);

        XSTS xsts;
        try (InputStream inputStream = new SequenceInputStream(new FileInputStream(filePath),
                new FileInputStream(propPath))) {
            xsts = XstsDslManager.createXsts(inputStream);
        }

<<<<<<< HEAD
        final XstsConfig<?, ?, ?> configuration = new XstsConfigBuilder(domain,
                XstsConfigBuilder.Refinement.SEQ_ITP, Z3SolverFactory.getInstance(),
                Z3SolverFactory.getInstance()).initPrec(XstsConfigBuilder.InitPrec.CTRL)
                .optimizeStmts(XstsConfigBuilder.OptimizeStmts.ON)
                .predSplit(XstsConfigBuilder.PredSplit.CONJUNCTS).maxEnum(250)
                .autoExpl(XstsConfigBuilder.AutoExpl.NEWOPERANDS).logger(logger).build(xsts);
        final SafetyResult<?, ?> status = configuration.check();
        if (safe) {
            assertTrue(status.isSafe());
        } else {
            assertTrue(status.isUnsafe());
        }
    }
=======
		final Logger logger = new ConsoleLogger(Level.SUBSTEP);

		XSTS xsts;
		try (InputStream inputStream = new SequenceInputStream(new FileInputStream(filePath), new FileInputStream(propPath))) {
			xsts = XstsDslManager.createXsts(inputStream);
		}

		var init = StmtUtils.toExpr(xsts.getInit(), VarIndexingFactory.indexing(0));
		Expr<BoolType> ini;


		Expr<BoolType> initExpr = init.getExprs().iterator().next();
		ini = And(initExpr,xsts.getInitFormula());
		var firstIndex= init.getIndexing();

		var merged = Stmts.SequenceStmt(List.of(xsts.getEnv(), xsts.getTran()));
		StmtUnfoldResult trans = StmtUtils.toExpr(merged, VarIndexingFactory.indexing(0));
		Expr<BoolType> transExpr = trans.getExprs().iterator().next();
		var offset= trans.getIndexing();

		var action = XstsAction.create(merged);

		var checker = new KIndChecker2<XstsState<ExplState>, XstsAction>(transExpr, ini, xsts.getProp(), 50,Z3SolverFactory.getInstance().createSolver(),Z3SolverFactory.getInstance().createSolver(),firstIndex,offset,(x)->XstsState.of(ExplState.of(x), false, true),xsts.getVars());
		var old = new Xsts_K_induction();
		//final XstsConfig<?, ?, ?> configuration = new XstsConfigBuilder(domain, XstsConfigBuilder.Refinement.SEQ_ITP, Z3SolverFactory.getInstance()).initPrec(XstsConfigBuilder.InitPrec.CTRL).optimizeStmts(XstsConfigBuilder.OptimizeStmts.ON).predSplit(XstsConfigBuilder.PredSplit.CONJUNCTS).maxEnum(250).autoExpl(XstsConfigBuilder.AutoExpl.NEWOPERANDS).logger(logger).build(xsts);
		final SafetyResult<?, ?> status = checker.check(null);
		//final SafetyResult<?, ?> status = old.check(xsts,50,Z3SolverFactory.getInstance().createSolver());
		if (safe) {
			assertTrue(status.isSafe());
		} else {
			assertTrue(status.isUnsafe());
		}
	}
>>>>>>> 727693816 (loopcheck fixed, xsts input fixed)

}
