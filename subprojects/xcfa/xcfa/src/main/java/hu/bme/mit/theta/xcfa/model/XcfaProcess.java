/*
 * Copyright 2021 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package hu.bme.mit.theta.xcfa.model;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.xcfa.passes.XcfaPassManager;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

/*
 * Process subclass
 */
@SuppressWarnings("unused")
public final class XcfaProcess {
    private static final String LABEL = "process";
    private final String name;
    private final ImmutableList<VarDecl<?>> params;
    private final ImmutableMap<VarDecl<?>, Optional<LitExpr<?>>> threadLocalVars;
    private final ImmutableList<XcfaProcedure> procedures;
    private final XcfaProcedure mainProcedure;
    private final XCFA parent;
    private final Tuple2<XcfaEdge, XcfaLabel.StartThreadXcfaLabel> threadStartStmt;


    private XcfaProcess(final Builder builder, XCFA parent) {
        params = ImmutableList.copyOf(builder.params);
        threadLocalVars = ImmutableMap.copyOf(builder.threadLocalVars);
        procedures = builder.procedures.stream().map(builder1 -> builder1.build(this)).collect(ImmutableList.toImmutableList());
        mainProcedure = builder.mainProcedure.build(this);
        name = builder.name == null ? mainProcedure.getName() : builder.name;
        threadStartStmt = null;
        this.parent = parent;
    }

    public static Builder builder() {
        return new Builder();
    }

    public String toDot(Collection<String> cexLocations, Collection<XcfaEdge> cexEdges) {
        StringBuilder ret = new StringBuilder();
        int cnt = 0;
        for (XcfaProcedure procedure : getProcedures()) {
            ret.append("subgraph cluster").append(cnt++).append("{\n");
            ret.append(procedure.toDot(cexLocations, cexEdges));
            ret.append("}\n");
        }
        return ret.toString();
    }

    public List<VarDecl<?>> getParams() {
        return params;
    }

    public List<VarDecl<?>> getThreadLocalVars() {
        return List.copyOf(threadLocalVars.keySet());
    }

    public Optional<LitExpr<?>> getInitValue(VarDecl<?> varDecl) {
        return threadLocalVars.get(varDecl);
    }

    public List<XcfaProcedure> getProcedures() {
        return procedures;
    }

    public XcfaProcedure getMainProcedure() {
        return mainProcedure;
    }

    public String getName() {
        return name;
    }

    public XCFA getParent() {
        return parent;
    }

    public Tuple2<XcfaEdge, XcfaLabel.StartThreadXcfaLabel> getThreadStartStmt() {
        return threadStartStmt;
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder().add(LABEL).add(name).toString();
    }

    public static final class Builder {
        private final List<VarDecl<?>> params;
        private final Map<VarDecl<?>, Optional<LitExpr<?>>> threadLocalVars;
        private final List<XcfaProcedure.Builder> procedures;
        private XcfaProcedure.Builder mainProcedure;
        private String name;

        private XcfaProcess built = null;

        private Builder() {
            params = new ArrayList<>();
            threadLocalVars = new LinkedHashMap<>();
            procedures = new ArrayList<>();
        }

        private void checkNotBuilt() {
            checkState(built == null, "A Process was already built.");
        }

        // params
        public List<VarDecl<?>> getParams() {
            return params;
        }

        public void createParam(final VarDecl<?> param) {
            checkNotBuilt();
            params.add(param);
        }

        // threadLocalVars
        public Map<VarDecl<?>, Optional<LitExpr<?>>> getThreadLocalVars() {
            return threadLocalVars;
        }

        public void createVar(final VarDecl<?> var, final LitExpr<?> initValue) {
            checkNotBuilt();
            threadLocalVars.put(var, Optional.ofNullable(initValue));
        }

        // procedures
        public List<XcfaProcedure.Builder> getProcedures() {
            return procedures;
        }

        public void addProcedure(final XcfaProcedure.Builder procedure) {
            checkNotBuilt();
            procedures.add(procedure);
        }

        // mainProcedure
        public XcfaProcedure.Builder getMainProcedure() {
            return mainProcedure;
        }

        public void setMainProcedure(final XcfaProcedure.Builder mainProcedure) {
            checkNotBuilt();
            checkArgument(procedures.contains(mainProcedure), "'procedures' does not contain main procedure");
            this.mainProcedure = mainProcedure;
        }

        // name

        public String getName() {
            return name;
        }

        public void setName(final String name) {
            checkNotBuilt();
            this.name = name;
        }

        public XcfaProcess build(XCFA parent) {
            if(built != null) return built;

            checkState(mainProcedure != null, "Main procedure must be set.");
            Builder builder = XcfaPassManager.run(this);
            XcfaProcess process = new XcfaProcess(builder, parent);
            built = process;
            return process;
        }
    }
}
