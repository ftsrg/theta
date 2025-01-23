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
package hu.bme.mit.theta.analysis.algorithm.mdd;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Leq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static org.junit.Assert.assertEquals;

import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.ExprLatticeDefinition;
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.MddExpressionTemplate;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.SolverPool;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import java.util.Set;
import org.junit.Test;

public class MddExpressionTest {

    @Test
    public void exprNodeTest1() {

        MddGraph<Expr> mddGraph =
                JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr());
        MddVariableOrder varOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);

        ConstDecl<IntType> declX = Decls.Const("x", Int());
        ConstDecl<IntType> declY = Decls.Const("y", Int());
        ConstDecl<IntType> declZ = Decls.Const("z", Int());

        MddVariable z = varOrder.createOnTop(MddVariableDescriptor.create(declZ, 0));
        MddVariable y = varOrder.createOnTop(MddVariableDescriptor.create(declY, 0));
        MddVariable x = varOrder.createOnTop(MddVariableDescriptor.create(declX, 0));

        // x >= 2 && y = x + 1 && x <= 6
        Expr<BoolType> expr =
                And(
                        Geq(declX.getRef(), Int(2)),
                        Eq(declY.getRef(), Add(declX.getRef(), Int(1))),
                        Leq(declX.getRef(), Int(6)));

        SolverPool solverPool = new SolverPool(Z3LegacySolverFactory.getInstance());
        MddNode rootNode = x.checkInNode(MddExpressionTemplate.of(expr, o -> (Decl) o, solverPool));

        var interpreter = x.getNodeInterpreter(rootNode);

        var recursiveCursor = interpreter.cursor();
        recursiveCursor.moveNext();
        recursiveCursor.moveNext();
        recursiveCursor.moveNext();

        try (var childCursor = recursiveCursor.valueCursor()) {
            childCursor.moveNext();
            childCursor.moveNext();
        }

        recursiveCursor.moveNext();

        try (var childCursor2 = recursiveCursor.valueCursor()) {
            childCursor2.moveNext();
            childCursor2.moveNext();
        }

        recursiveCursor.moveNext();
        recursiveCursor.moveNext();

        final Set<Valuation> valuations = MddValuationCollector.collect(rootNode);

        assertEquals(valuations.size(), 5);
    }

    @Test
    public void exprNodeTest2() {

        MddGraph<Expr> mddGraph =
                JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr());
        MddVariableOrder varOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);

        ConstDecl<BoolType> declA = Decls.Const("a", Bool());
        ConstDecl<BoolType> declB = Decls.Const("b", Bool());
        ConstDecl<IntType> declX = Decls.Const("x", Int());

        MddVariable x = varOrder.createOnTop(MddVariableDescriptor.create(declX, 0));
        MddVariable b = varOrder.createOnTop(MddVariableDescriptor.create(declB, 2));
        MddVariable a = varOrder.createOnTop(MddVariableDescriptor.create(declA, 2));

        Expr<BoolType> expr =
                And(Or(declA.getRef(), Not(declB.getRef())), Eq(declX.getRef(), Int(2)));

        SolverPool solverPool = new SolverPool(Z3LegacySolverFactory.getInstance());
        MddNode rootNode = a.checkInNode(MddExpressionTemplate.of(expr, o -> (Decl) o, solverPool));

        for (var c = rootNode.cursor(); c.moveNext(); ) {}

        var node2 = rootNode.get(0);

        for (var c = node2.cursor(); c.moveNext(); ) {}

        var node3 = node2.get(0);

        for (var c = node3.cursor(); c.moveNext(); ) {}

        var node4 = rootNode.get(1);

        for (var c = node4.cursor(); c.moveNext(); ) {}

        final Set<Valuation> valuations = MddValuationCollector.collect(rootNode);

        // TODO This might be 2 if default values are enabled
        assertEquals(valuations.size(), 3);
    }

    @Test
    public void exprNodeTest3() {

        // TODO need to fix nodeinterpreters and cursors

        MddGraph<Expr> mddGraph =
                JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr());
        MddVariableOrder varOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);

        ConstDecl<IntType> declX = Decls.Const("x", Int());
        ConstDecl<IntType> declY = Decls.Const("y", Int());
        ConstDecl<IntType> declZ = Decls.Const("z", Int());

        MddVariable z = varOrder.createOnTop(MddVariableDescriptor.create(declZ, 0));
        MddVariable y = varOrder.createOnTop(MddVariableDescriptor.create(declY, 0));
        MddVariable x = varOrder.createOnTop(MddVariableDescriptor.create(declX, 0));

        // y >= 2 && z = y + 1 && y <= 6
        Expr<BoolType> expr =
                And(
                        Geq(declY.getRef(), Int(2)),
                        Eq(declZ.getRef(), Add(declY.getRef(), Int(1))),
                        Leq(declY.getRef(), Int(6)));

        SolverPool solverPool = new SolverPool(Z3LegacySolverFactory.getInstance());
        MddNode rootNode = x.checkInNode(MddExpressionTemplate.of(expr, o -> (Decl) o, solverPool));

        var interpreter = x.getNodeInterpreter(rootNode);

        var recursiveCursor = interpreter.cursor();
        recursiveCursor.moveNext();

        try (var childCursor = recursiveCursor.valueCursor()) {
            childCursor.moveNext();
            childCursor.moveNext();
            childCursor.moveNext();
            childCursor.moveNext();
        }

        final Set<Valuation> valuations = MddValuationCollector.collect(rootNode);

        assertEquals(valuations.size(), 5);
    }

    @Test
    public void exprNodeTest4() {

        MddGraph<Expr> mddGraph =
                JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr());
        MddVariableOrder varOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);

        ConstDecl<IntType> declX = Decls.Const("x", Int());
        ConstDecl<IntType> declY = Decls.Const("y", Int());
        ConstDecl<IntType> declZ = Decls.Const("z", Int());

        MddVariable y = varOrder.createOnTop(MddVariableDescriptor.create(declY, 0));
        MddVariable x = varOrder.createOnTop(MddVariableDescriptor.create(declX, 0));

        // x >= 2 && y = x + 1 && x <= 6 && z = y + 2
        Expr<BoolType> expr =
                And(
                        Geq(declX.getRef(), Int(2)),
                        Eq(declY.getRef(), Add(declX.getRef(), Int(1))),
                        Leq(declX.getRef(), Int(6)),
                        Eq(declZ.getRef(), Add(declY.getRef(), Int(2))));

        SolverPool solverPool = new SolverPool(Z3LegacySolverFactory.getInstance());
        MddNode rootNode = x.checkInNode(MddExpressionTemplate.of(expr, o -> (Decl) o, solverPool));

        var interpreter = x.getNodeInterpreter(rootNode);

        var recursiveCursor = interpreter.cursor();
        recursiveCursor.moveNext();
        recursiveCursor.moveNext();
        recursiveCursor.moveNext();

        try (var childCursor = recursiveCursor.valueCursor()) {
            childCursor.moveNext();
            childCursor.moveNext();
        }

        recursiveCursor.moveNext();

        try (var childCursor2 = recursiveCursor.valueCursor()) {
            childCursor2.moveNext();
            childCursor2.moveNext();
        }

        recursiveCursor.moveNext();
        recursiveCursor.moveNext();

        final Set<Valuation> valuations = MddValuationCollector.collect(rootNode);

        assertEquals(valuations.size(), 5);
    }

    @Test
    public void exprNodeTest5() {

        MddGraph<Expr> mddGraph =
                JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr());
        MddVariableOrder varOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);

        ConstDecl<IntType> declX = Decls.Const("x", Int());
        ConstDecl<IntType> declY = Decls.Const("y", Int());
        ConstDecl<IntType> declZ = Decls.Const("z", Int());

        MddVariable z = varOrder.createOnTop(MddVariableDescriptor.create(declZ, 0));
        MddVariable y = varOrder.createOnTop(MddVariableDescriptor.create(declY, 0));
        MddVariable x = varOrder.createOnTop(MddVariableDescriptor.create(declX, 0));

        // x = y && y = z && z = 2
        Expr<BoolType> expr =
                And(
                        Eq(declX.getRef(), declY.getRef()),
                        And(Eq(declY.getRef(), declZ.getRef()), Eq(declZ.getRef(), Int(2))));

        SolverPool solverPool = new SolverPool(Z3LegacySolverFactory.getInstance());
        MddNode rootNode = x.checkInNode(MddExpressionTemplate.of(expr, o -> (Decl) o, solverPool));

        var interpreter = x.getNodeInterpreter(rootNode);

        var recursiveCursor = interpreter.cursor();
        recursiveCursor.moveNext();
        recursiveCursor.moveNext();
        recursiveCursor.moveNext();

        final Set<Valuation> valuations = MddValuationCollector.collect(rootNode);

        assertEquals(valuations.size(), 1);
    }

    @Test
    public void exprNodeTest6() {

        MddGraph<Expr> mddGraph =
                JavaMddFactory.getDefault().createMddGraph(ExprLatticeDefinition.forExpr());
        MddVariableOrder varOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph);

        ConstDecl<IntType> declX = Decls.Const("x", Int());
        ConstDecl<IntType> declY = Decls.Const("y", Int());
        ConstDecl<IntType> declZ = Decls.Const("z", Int());

        MddVariable z = varOrder.createOnTop(MddVariableDescriptor.create(declZ, 0));
        MddVariable y = varOrder.createOnTop(MddVariableDescriptor.create(declY, 0));
        MddVariable x = varOrder.createOnTop(MddVariableDescriptor.create(declX, 0));

        // x >= 0 && x <= 2 && y >= x && y <= x + 2 && z >= y && z <= y + 2
        Expr<BoolType> expr =
                And(
                        And(Geq(declX.getRef(), Int(0)), Leq(declX.getRef(), Int(2))),
                        And(
                                Geq(declY.getRef(), declX.getRef()),
                                Leq(declY.getRef(), Add(declX.getRef(), Int(2)))),
                        And(
                                Geq(declZ.getRef(), declY.getRef()),
                                Leq(declZ.getRef(), Add(declY.getRef(), Int(2)))));

        SolverPool solverPool = new SolverPool(Z3LegacySolverFactory.getInstance());
        MddNode rootNode = x.checkInNode(MddExpressionTemplate.of(expr, o -> (Decl) o, solverPool));

        var interpreter = x.getNodeInterpreter(rootNode);

        var recursiveCursor = interpreter.cursor();
        recursiveCursor.moveNext();

        try (var childCursor = recursiveCursor.valueCursor()) {
            childCursor.moveNext();
            childCursor.moveNext();
        }

        recursiveCursor.moveNext();

        try (var childCursor2 = recursiveCursor.valueCursor()) {
            childCursor2.moveNext();
            childCursor2.moveNext();
        }

        recursiveCursor.moveNext();
        recursiveCursor.moveNext();

        final Set<Valuation> valuations = MddValuationCollector.collect(rootNode);

        assertEquals(27, valuations.size());
    }
}
