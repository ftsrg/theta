package hu.bme.mit.theta.xcfa;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.LitExpr;

import java.util.*;

import static com.google.common.base.Preconditions.*;

/*
 * Process subclass
 */
@SuppressWarnings("unused")
public final class XcfaProcess implements hu.bme.mit.theta.mcm.graphfilter.interfaces.Process {
    private XCFA parent;

    private final String name;
    private final ImmutableList<VarDecl<?>> params;
    private final ImmutableMap<VarDecl<?>, Optional<LitExpr<?>>> threadLocalVars;
    private final ImmutableList<XcfaProcedure> procedures;
    private final XcfaProcedure mainProcedure;

    private static final String LABEL = "process";


    private XcfaProcess(final Builder builder) {
        params = ImmutableList.copyOf(builder.params);
        threadLocalVars = ImmutableMap.copyOf(builder.threadLocalVars);
        procedures = ImmutableList.copyOf(builder.procedures);
        procedures.forEach(procedure -> procedure.setParent(this));
        mainProcedure = builder.mainProcedure;
        name = builder.name;
    }

    public String toDot() {
        StringBuilder ret = new StringBuilder();
        int cnt = 0;
        for (XcfaProcedure procedure : getProcedures()) {
            ret.append("subgraph cluster").append(cnt++).append("{\n");
            ret.append(procedure.toDot());
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

    void setParent(XCFA xcfa) {
        this.parent = xcfa;
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder().add(LABEL).add(name).toString();
    }

    public static Builder builder() {
        return new Builder();
    }

    public static final class Builder {
        private final List<VarDecl<?>> params;
        private final Map<VarDecl<?>, Optional<LitExpr<?>>> threadLocalVars;
        private final List<XcfaProcedure> procedures;
        private XcfaProcedure mainProcedure;
        private String name;

        private boolean built;

        private Builder() {
            built = false;
            params = new ArrayList<>();
            threadLocalVars = new HashMap<>();
            procedures = new ArrayList<>();
        }

        private void checkNotBuilt() {
            checkState(!built, "A Process was already built.");
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
        public List<XcfaProcedure> getProcedures() {
            return procedures;
        }

        public void addProcedure(final XcfaProcedure procedure) {
            checkNotBuilt();
            procedures.add(procedure);
        }

        // mainProcedure
        public XcfaProcedure getMainProcedure() {
            return mainProcedure;
        }

        public void setMainProcedure(final XcfaProcedure mainProcedure) {
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

        public XcfaProcess build() {
            checkNotBuilt();
            checkState(mainProcedure != null, "Main procedure must be set.");
            XcfaProcess process = new XcfaProcess(this);
            built = true;
            return process;
        }
    }
}
