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
import hu.bme.mit.theta.xcfa.passes.ChcPasses;
import kotlin.Pair;
import org.antlr.v4.runtime.RuleContext;

import java.util.*;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.frontend.chc.ChcUtils.*;

public class ChcBackwardXcfaBuilder extends CHCBaseVisitor<Object> implements ChcXcfaBuilder {
    private final Map<String, XcfaProcedureBuilder> procedures = new HashMap<>();
    private XcfaBuilder xcfaBuilder;
    private int callCount = 0;

    @Override
    public XcfaBuilder buildXcfa(CHCParser parser) {
        xcfaBuilder = new XcfaBuilder("chc");

        visit(parser.benchmark());

//        xcfaBuilder.addProcess(procBuilder);
//        xcfaBuilder.setMainProcess(procBuilder);
        return xcfaBuilder;
    }

    @Override
    public Object visitFun_decl(CHCParser.Fun_declContext ctx) {
        String name = ctx.symbol().getText();
        if (ctx.symbol().quotedSymbol() != null) name = name.replaceAll("\\|", "");
        XcfaProcedureBuilder builder = createProcedure(name);

        int i = 0;
        for (CHCParser.SortContext sort : ctx.sort()) {
            String varName = name + "_" + i++;
            Type type = transformSort(sort);
            builder.addParam(Decls.Var(varName, type), ParamDirection.IN);
            transformConst(Decls.Const(varName, type), true);
        }

        procedures.put(name, builder);
        procedures.put(ctx.symbol().getText(), builder);
        return super.visitFun_decl(ctx);
    }

    @Override
    public Object visitChc_assert(CHCParser.Chc_assertContext ctx) {
        XcfaProcedureBuilder procedure;
        if (ctx.chc_tail() != null) {
            procedure = procedures.get(ctx.chc_head().u_pred_atom().u_predicate().getText());
            Map<String, VarDecl<?>> vars = createVars(procedure, ctx.var_decl());
            int i = 0;
            for (Pair<VarDecl<?>, ParamDirection> param : procedure.getParams()) {
                if (param.getSecond() != ParamDirection.OUT)
                    vars.put(ctx.chc_head().u_pred_atom().symbol(i++).getText(), param.getFirst());
            }
            XcfaLocation middle = createLocation(procedure);
            XcfaEdge edge = new XcfaEdge(procedure.getInitLoc(), middle, new SequenceLabel(getTailConditionLabels(ctx.chc_tail(), vars)));
            procedure.addEdge(edge);
            createCalls(procedure, middle, procedure.getFinalLoc().get(), ctx.chc_tail().u_pred_atom(), vars);
        } else {
            String procName;
            if (ctx.chc_head() != null) {
                procName = ctx.chc_head().u_pred_atom().u_predicate().getText();
            } else {
                procName = ctx.u_predicate().getText();
            }
            procedure = procedures.get(procName);
            Stmt returnTrue = AssignStmt.create(getOutParam(procedure), BoolLitExpr.of(true));
            XcfaEdge edge = new XcfaEdge(procedure.getInitLoc(), procedure.getFinalLoc().get(), new StmtLabel(returnTrue, EmptyMetaData.INSTANCE));
            procedure.addEdge(edge);
        }
        return super.visitChc_assert(ctx);
    }

    @Override
    public Object visitChc_query(CHCParser.Chc_queryContext ctx) {
        XcfaProcedureBuilder mainProcedure = createProcedure("query");
        xcfaBuilder.addEntryPoint(mainProcedure, new ArrayList<>());

        Map<String, VarDecl<?>> vars = createVars(mainProcedure, ctx.var_decl());
        XcfaLocation middle = createLocation(mainProcedure);
        XcfaEdge edge = new XcfaEdge(mainProcedure.getInitLoc(), middle, new SequenceLabel(getTailConditionLabels(ctx.chc_tail(), vars)));
        mainProcedure.addEdge(edge);
        createCalls(mainProcedure, middle, mainProcedure.getErrorLoc().get(), ctx.chc_tail().u_pred_atom(), vars);
        return super.visitChc_query(ctx);
    }

    private int uniqeCounter = 0;

    private XcfaLocation createLocation(XcfaProcedureBuilder builder) {
        XcfaLocation location = new XcfaLocation("l_" + uniqeCounter++);
        builder.addLoc(location);
        return location;
    }

    private XcfaProcedureBuilder createProcedure(String procName) {
        XcfaProcedureBuilder builder = new XcfaProcedureBuilder(procName, new ChcPasses());
        builder.setName(procName);
        builder.addParam(Decls.Var(procName + "_ret", Bool()), ParamDirection.OUT);

        builder.createInitLoc();
        builder.createErrorLoc();
        builder.createFinalLoc();

        xcfaBuilder.addProcedure(builder);
        return builder;
    }

    private VarDecl<?> getOutParam(XcfaProcedureBuilder procedure) {
        Optional<Pair<VarDecl<?>, ParamDirection>> param = procedure.getParams()
                .stream().filter(entry -> entry.getSecond() == ParamDirection.OUT).findAny();
        return param.map(Pair::getFirst).orElse(null);
    }

    private void createCalls(XcfaProcedureBuilder builder, XcfaLocation start, XcfaLocation end, List<CHCParser.U_pred_atomContext> uPreds, Map<String, VarDecl<?>> localVars) {
        XcfaLocation from = start;
        for (CHCParser.U_pred_atomContext uPred : uPreds) {
            XcfaLocation middle = createLocation(builder);
            XcfaLocation to = createLocation(builder);

            XcfaProcedureBuilder calledProcedure = procedures.get(uPred.u_predicate().getText());
            VarDecl<BoolType> ret = Decls.Var(calledProcedure.getName() + "_ret_" + callCount++, Bool());
            builder.addVar(ret);
            localVars.put(ret.getName(), ret);
            List<String> paramNames = new ArrayList<>(uPred.symbol().stream().map(RuleContext::getText).toList());
            paramNames.add(0, ret.getName());
            List<? extends Expr<?>> params = paramNames.stream().map(s -> localVars.get(s).getRef()).toList();

            XcfaEdge callEdge = new XcfaEdge(from, middle, new InvokeLabel(calledProcedure.getName(), params, EmptyMetaData.INSTANCE));
            builder.addEdge(callEdge);

            XcfaEdge assertEdge = new XcfaEdge(middle, to, new StmtLabel(AssumeStmt.of(ret.getRef()), EmptyMetaData.INSTANCE));
            builder.addEdge(assertEdge);

            from = to;
        }
        Stmt returnTrue = AssignStmt.create(getOutParam(builder), BoolLitExpr.of(true));
        XcfaEdge edge = new XcfaEdge(from, end, new StmtLabel(returnTrue, EmptyMetaData.INSTANCE));
        builder.addEdge(edge);
    }
}
