/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.MddValuationCollector;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.SolverPool;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.ExprLatticeDefinition;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.MddExpressionTemplate;
import hu.bme.mit.theta.analysis.utils.MddNodeVisualizer;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.dsl.XstsDslManager;
import org.junit.Test;

import java.io.*;
import java.util.Set;

import static org.junit.Assert.assertEquals;


public class XstsInitExprNodeTest {

    @Test
    public void testInit() throws IOException {

        XSTS xsts;
        try (InputStream inputStream = new SequenceInputStream(new FileInputStream("src/test/resources/model/trafficlight.xsts"), new FileInputStream("src/test/resources/property/green_and_red.prop"))) {
            xsts = XstsDslManager.createXsts(inputStream);
        }

        MddGraph<Expr> mddGraph = JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr());
        MddVariableOrder varOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);

        Expr<BoolType> expr = PathUtils.unfold(xsts.getInitFormula(), 0);

        MddVariable lastVar = null;
        for (var v : xsts.getVars()) {
            lastVar = varOrder.createOnTop(hu.bme.mit.delta.mdd.MddVariableDescriptor.create(v.getConstDecl(0), 0));
        }

        SolverPool solverPool = new SolverPool(Z3LegacySolverFactory.getInstance());
        MddNode rootNode = lastVar.checkInNode(MddExpressionTemplate.of(expr, o -> (Decl) o, solverPool));

        var recursiveCursor = rootNode.cursor();
        recursiveCursor.moveNext();

        final Set<Valuation> valuations = MddValuationCollector.collect(rootNode);
        System.out.println(valuations);

        assertEquals(valuations.size(), 1);

        final Graph graph = new MddNodeVisualizer(XstsInitExprNodeTest::nodeToString).visualize(rootNode);
        try {
            GraphvizWriter.getInstance().writeFile(graph, "/home/milan/programming/mdd.dot");
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }


    }

    private static String nodeToString(MddNode node) {
        return node instanceof MddNode.Terminal ? ((MddNode.Terminal<?>) node).getTerminalData().toString() : node.getRepresentation().toString();
    }

}
