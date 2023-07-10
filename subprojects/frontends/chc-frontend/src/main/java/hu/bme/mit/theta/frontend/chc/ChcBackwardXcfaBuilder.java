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
package hu.bme.mit.theta.frontend.chc;

import hu.bme.mit.theta.chc.frontend.dsl.gen.CHCBaseVisitor;
import hu.bme.mit.theta.chc.frontend.dsl.gen.CHCParser;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xcfa.model.*;
import org.antlr.v4.runtime.RuleContext;

import java.util.*;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.frontend.chc.ChcUtils.*;

public class ChcBackwardXcfaBuilder extends CHCBaseVisitor<Object> implements ChcXcfaBuilder {

    private final Map<String, XcfaProcedure.Builder> procedures = new HashMap<>();
    private XcfaProcess.Builder procBuilder;
    private int callCount = 0;

    @Override
    public XCFA.Builder buildXcfa(CHCParser parser) {
        XCFA.Builder xcfaBuilder = XCFA.builder();
        xcfaBuilder.setDynamic(true);
        procBuilder = XcfaProcess.builder();

        visit(parser.benchmark());

        xcfaBuilder.addProcess(procBuilder);
        xcfaBuilder.setMainProcess(procBuilder);
        return xcfaBuilder;
    }

    @Override
    public Object visitFun_decl(CHCParser.Fun_declContext ctx) {
        String name = ctx.symbol().getText();
        if (ctx.symbol().quotedSymbol() != null) {
            name = name.replaceAll("\\|", "");
        }
        XcfaProcedure.Builder builder = createProcedure(name);

        int i = 0;
        for (CHCParser.SortContext sort : ctx.sort()) {
            String varName = name + "_" + i++;
            Type type = transformSort(sort);
            builder.createParam(XcfaProcedure.Direction.IN, Decls.Var(varName, type));
            transformConst(Decls.Const(varName, type), true);
        }

        procedures.put(name, builder);
        procedures.put(ctx.symbol().getText(), builder);
        return super.visitFun_decl(ctx);
    }

    @Override
    public Object visitChc_assert(CHCParser.Chc_assertContext ctx) {
        XcfaProcedure.Builder procedure;
        if (ctx.chc_tail() != null) {
            procedure = procedures.get(ctx.chc_head().u_pred_atom().u_predicate().getText());
            Map<String, VarDecl<?>> vars = createVars(procedure, ctx.var_decl());
            int i = 0;
            for (Map.Entry<VarDecl<?>, XcfaProcedure.Direction> param : procedure.getParams()
                    .entrySet()) {
                if (param.getValue() != XcfaProcedure.Direction.OUT) {
                    vars.put(ctx.chc_head().u_pred_atom().symbol(i++).getText(), param.getKey());
                }
            }
            XcfaLocation middle = createLocation(procedure);
            XcfaEdge edge = XcfaEdge.of(procedure.getInitLoc(), middle,
                    getTailConditionLabels(ctx.chc_tail(), vars));
            procedure.addEdge(edge);
            createCalls(procedure, middle, procedure.getFinalLoc(), ctx.chc_tail().u_pred_atom(),
                    vars);
        } else {
            String procName;
            if (ctx.chc_head() != null) {
                procName = ctx.chc_head().u_pred_atom().u_predicate().getText();
            } else {
                procName = ctx.u_predicate().getText();
            }
            procedure = procedures.get(procName);
            Stmt returnTrue = AssignStmt.create(getOutParam(procedure), BoolLitExpr.of(true));
            XcfaEdge edge = XcfaEdge.of(procedure.getInitLoc(), procedure.getFinalLoc(),
                    List.of(XcfaLabel.Stmt(returnTrue)));
            procedure.addEdge(edge);
        }
        return super.visitChc_assert(ctx);
    }

    @Override
    public Object visitChc_query(CHCParser.Chc_queryContext ctx) {
        XcfaProcedure.Builder mainProcedure = createProcedure("query");
        procBuilder.setMainProcedure(mainProcedure);

        Map<String, VarDecl<?>> vars = createVars(mainProcedure, ctx.var_decl());
        XcfaLocation middle = createLocation(mainProcedure);
        XcfaEdge edge = XcfaEdge.of(mainProcedure.getInitLoc(), middle,
                getTailConditionLabels(ctx.chc_tail(), vars));
        mainProcedure.addEdge(edge);
        createCalls(mainProcedure, middle, mainProcedure.getErrorLoc(),
                ctx.chc_tail().u_pred_atom(), vars);
        return super.visitChc_query(ctx);
    }

    private XcfaLocation createLocation(XcfaProcedure.Builder builder) {
        XcfaLocation location = XcfaLocation.create("l_" + XcfaLocation.uniqeCounter());
        builder.addLoc(location);
        return location;
    }

    private XcfaProcedure.Builder createProcedure(String procName) {
        XcfaProcedure.Builder builder = XcfaProcedure.builder();
        builder.setName(procName);
        builder.createParam(XcfaProcedure.Direction.OUT, Decls.Var(procName + "_ret", Bool()));
        builder.setRetType(Bool());

        XcfaLocation initLocation = XcfaLocation.create("Init_" + procName);
        builder.addLoc(initLocation);
        builder.setInitLoc(initLocation);

        XcfaLocation errorLocation = XcfaLocation.create("Err_" + procName);
        builder.addLoc(errorLocation);
        builder.setErrorLoc(errorLocation);

        XcfaLocation finalLocation = XcfaLocation.create("Final_" + procName);
        builder.addLoc(finalLocation);
        builder.setFinalLoc(finalLocation);

        procBuilder.addProcedure(builder);
        return builder;
    }

    private VarDecl<?> getOutParam(XcfaProcedure.Builder procedure) {
        Optional<Map.Entry<VarDecl<?>, XcfaProcedure.Direction>> param = procedure.getParams()
                .entrySet()
                .stream().filter(entry -> entry.getValue() == XcfaProcedure.Direction.OUT).findAny();
        return param.map(Map.Entry::getKey).orElse(null);
    }

    private void createCalls(XcfaProcedure.Builder builder, XcfaLocation start, XcfaLocation end,
                             List<CHCParser.U_pred_atomContext> uPreds, Map<String, VarDecl<?>> localVars) {
        XcfaLocation from = start;
        for (CHCParser.U_pred_atomContext uPred : uPreds) {
            XcfaLocation middle = createLocation(builder);
            XcfaLocation to = createLocation(builder);

            XcfaProcedure.Builder calledProcedure = procedures.get(uPred.u_predicate().getText());
            VarDecl<BoolType> ret = Decls.Var(calledProcedure.getName() + "_ret_" + callCount++,
                    Bool());
            builder.createVar(ret, null);
            localVars.put(ret.getName(), ret);
            List<String> paramNames = new ArrayList<>(
                    uPred.symbol().stream().map(RuleContext::getText).toList());
            paramNames.add(0, ret.getName());
            List<? extends Expr<?>> params = paramNames.stream().map(s -> localVars.get(s).getRef())
                    .toList();

            XcfaEdge callEdge = XcfaEdge.of(from, middle, List.of(
                    XcfaLabel.ProcedureCall((List<Expr<?>>) params, calledProcedure.getName())));
            builder.addEdge(callEdge);

            XcfaEdge assertEdge = XcfaEdge.of(middle, to,
                    List.of(XcfaLabel.Stmt(AssumeStmt.of(ret.getRef()))));
            builder.addEdge(assertEdge);

            from = to;
        }
        Stmt returnTrue = AssignStmt.create(getOutParam(builder), BoolLitExpr.of(true));
        XcfaEdge edge = XcfaEdge.of(from, end, List.of(XcfaLabel.Stmt(returnTrue)));
        builder.addEdge(edge);
    }
}
