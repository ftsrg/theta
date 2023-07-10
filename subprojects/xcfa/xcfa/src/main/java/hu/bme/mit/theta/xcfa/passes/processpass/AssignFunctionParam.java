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

package hu.bme.mit.theta.xcfa.passes.processpass;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.xcfa.model.*;
import hu.bme.mit.theta.xcfa.passes.XcfaPassManager;
import hu.bme.mit.theta.xcfa.passes.procedurepass.UnusedVarRemovalPass;

import java.util.*;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.Stmt;
import static hu.bme.mit.theta.xcfa.passes.procedurepass.Utils.getNonModifiedVars;

public class AssignFunctionParam extends ProcessPass {

    private final List<XcfaEdge> edgesToAdd = new ArrayList<>();
    private final List<XcfaEdge> edgesToRemove = new ArrayList<>();
    private final Map<XcfaProcedure.Builder, Map<XcfaLabel.ProcedureCallXcfaLabel, XcfaProcedure.Builder>> procedureCalls = new LinkedHashMap<>();

    @Override
    public XcfaProcess.Builder run(XcfaProcess.Builder builder) {
        if (FunctionInlining.inlining == FunctionInlining.InlineFunctions.ON) {
            return builder;
        }
        XcfaProcess.Builder builtBuilder = buildProcesses(builder);
        for (XcfaProcedure.Builder procedure : builtBuilder.getProcedures()) {
            edgesToAdd.clear();
            edgesToRemove.clear();
            procedureCalls.clear();
            for (XcfaEdge edge : procedure.getEdges()) {
                for (XcfaLabel label : edge.getLabels()) {
                    if (label instanceof XcfaLabel.ProcedureCallXcfaLabel) {
                        XcfaLabel.ProcedureCallXcfaLabel callLabel = (XcfaLabel.ProcedureCallXcfaLabel) label;
                        Optional<XcfaProcedure.Builder> procedureOpt = builtBuilder.getProcedures()
                            .stream().filter(xcfaProcedure -> xcfaProcedure.getName()
                                .equals(callLabel.getProcedure())).findAny();
                        procedureOpt.ifPresent(calledProcedure -> {
                            assignParams(procedure, callLabel, calledProcedure);
                            if (calledProcedure.getRetType() != null) {
                                List<XcfaLabel> retStmts = getRetStmts(callLabel, calledProcedure);
                                assignReturns(procedure, edge, retStmts);
                            }
                        });
                    }
                }
            }
            edgesToRemove.forEach(procedure::removeEdge);
            edgesToAdd.forEach(procedure::addEdge);
            procedureCalls.forEach((calledProcedure, callLabels) -> callLabels.forEach(
                calledProcedure::addParamInitLoc));
        }

        return builtBuilder;
    }

    private XcfaProcess.Builder buildProcesses(XcfaProcess.Builder builder) {
        XcfaProcess.Builder newBuilder = XcfaProcess.builder();
        newBuilder.setName(builder.getName());
        newBuilder.getThreadLocalVars().putAll(builder.getThreadLocalVars());
        for (VarDecl<?> param : builder.getParams()) {
            newBuilder.createParam(param);
        }
        for (XcfaProcedure.Builder procBuilder : builder.getProcedures()) {
            Set<VarDecl<?>> usedVars = new LinkedHashSet<>();
            for (XcfaEdge edge : procBuilder.getEdges()) {
                for (XcfaLabel label : edge.getLabels()) {
                    usedVars.addAll(getNonModifiedVars(label));
                }
            }
            UnusedVarRemovalPass.removeUnusedVars(procBuilder, usedVars);
            newBuilder.addProcedure(XcfaPassManager.run(procBuilder));
            if (procBuilder == builder.getMainProcedure()) {
                newBuilder.setMainProcedure(procBuilder);
            }
        }
        return newBuilder;
    }

    private void assignParams(XcfaProcedure.Builder callingProcedure,
        XcfaLabel.ProcedureCallXcfaLabel callLabel, XcfaProcedure.Builder calledProcedure) {
        Map<XcfaLabel.ProcedureCallXcfaLabel, XcfaProcedure.Builder> callLabels = procedureCalls.getOrDefault(
            calledProcedure, new HashMap<>());
        callLabels.put(callLabel, callingProcedure);
        procedureCalls.put(calledProcedure, callLabels);
    }

    private void assignReturns(XcfaProcedure.Builder procedure, XcfaEdge edge,
        List<XcfaLabel> retStmts) {
        XcfaLocation middle = XcfaLocation.uniqeCopyOf(edge.getSource());
        procedure.addLoc(middle);
        edgesToRemove.add(edge);
        edgesToAdd.add(XcfaEdge.of(edge.getSource(), middle, edge.getLabels()));
        XcfaEdge retEdge = XcfaEdge.of(middle, edge.getTarget(), retStmts);
        FrontendMetadata.lookupMetadata(edge)
            .forEach((s, o) -> FrontendMetadata.create(retEdge, s, o));
        edgesToAdd.add(retEdge);
    }

    private List<XcfaLabel> getRetStmts(XcfaLabel.ProcedureCallXcfaLabel callLabel,
        XcfaProcedure.Builder calledProcedure) {
        List<XcfaLabel> retStmts = new ArrayList<>();
        int paramCnt = 0;
        for (Map.Entry<VarDecl<?>, XcfaProcedure.Direction> entry : calledProcedure.getParams()
            .entrySet()) {
            VarDecl<?> varDecl = entry.getKey();
            XcfaProcedure.Direction direction = entry.getValue();
            if (direction != XcfaProcedure.Direction.IN) {
                Expr<?> expr = callLabel.getParams().get(paramCnt);
                checkState(
                    expr instanceof RefExpr && ((RefExpr<?>) expr).getDecl() instanceof VarDecl<?>);
                retStmts.add(Stmt(
                    Assign(cast((VarDecl<?>) ((RefExpr<?>) expr).getDecl(), varDecl.getType()),
                        cast(varDecl.getRef(), varDecl.getType()))));
            }
            ++paramCnt;
        }
        return retStmts;
    }
}
