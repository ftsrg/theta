package hu.bme.mit.theta.cfa.analysis.alt.transform;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.cfa.XCFA;
import hu.bme.mit.theta.cfa.XCFA.Process.Procedure;
import hu.bme.mit.theta.cfa.dsl.CallStmt;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

class EmptyTransformation {
    protected final XCFA old;

    private final Map<Object, Object> cache = new HashMap<>();
    private final List<CallRegistration> callStmts = new ArrayList<>();

    EmptyTransformation(XCFA old) {
        this.old = old;
    }

    public final XCFA build() {
        var builder = XCFA.builder();
        old.getProcesses().forEach(
                p -> builder.addProcess(transformed(builder, p))
        );
        builder.setMainProcess(transformed(builder, old.getMainProcess()));
        old.getGlobalVars().forEach(builder::createVar);
        beforeBuild(builder);
        var result = builder.build();
        afterBuild(result);
        return result;
    }

    /**
     * Resolving circular dependencies.
     * Builder pattern prevents (a more) trivial solution.
     * The default implementation resolves CallStmts.
     * @param xcfa
     */
    protected void afterBuild(XCFA xcfa) {
        for (var reg : callStmts) {
            reg.newCall.setProcedure(cached(reg.oldProcedure).get());
        }
    }

    public final <R> Optional<R> cached(R r) {
        if (cache.containsKey(r))
            return Optional.of((R)cache.get(r));
        return Optional.empty();
    }

    public final <R> R transformed(Object builder, R val) {
        var cached = cached(val);
        if (cached.isPresent()) {
            return cached.get();
        }
        Object result = null;
        if (val instanceof XCFA.Process)
            result = copy((XCFA.Builder)builder, (XCFA.Process) val);
        else if (val instanceof XCFA.Process.Procedure)
            result = copy((XCFA.Process.Builder)builder, (XCFA.Process.Procedure) val);
        else if (val instanceof XCFA.Process.Procedure.Location)
            result = copy((XCFA.Process.Procedure.Builder)builder, (XCFA.Process.Procedure.Location) val);
        else if (val instanceof XCFA.Process.Procedure.Edge)
            result = copy((XCFA.Process.Procedure.Builder)builder, (XCFA.Process.Procedure.Edge) val);
        else if (val instanceof VarDecl)
            result = copy(builder, (VarDecl<? extends Type>) val);
        else {
            Preconditions.checkState(false, "Do not know how to copy the instance of type" +
                    val.getClass().getName());
        }
        cache.put(val, result);
        return (R) result;
    }

    /**
     * Contains a registration to fill the newCall's procedure link to the
     * new instance of the old procedure.
     * @author laszlo.radnai
     *
     */
    private class CallRegistration {
        private final CallStmt newCall;
        private final Procedure oldProcedure;
        CallRegistration(CallStmt newCall, Procedure oldProcedure) {
            this.newCall = newCall;
            this.oldProcedure = oldProcedure;
        }
    }

    final protected void registerCallStmt(CallStmt newCall, Procedure oldProcedure) {
        callStmts.add(new CallRegistration(newCall, oldProcedure));
    }

    /**
     * Copies edges.
     * Caches CallStmts for after building to point to the new instance of the procedure.
     * Edge copy overriders should register CallStmts when not calling super.copy()
     * @param builder
     * @param val
     * @return
     */
    protected XCFA.Process.Procedure.Edge copy(XCFA.Process.Procedure.Builder builder, XCFA.Process.Procedure.Edge val) {
        boolean needsNewInstance = false;
        for (var stmt : val.getStmts()) {
            if (stmt instanceof CallStmt) {
                needsNewInstance = true;
                break;
            }
        }
        final List<Stmt> stmts;
        if (needsNewInstance) {
            stmts = new ArrayList<>();
            for (var stmt : val.getStmts()) {
                if (stmt instanceof CallStmt) {
                    var newCall = new CallStmt(((CallStmt) stmt).getResultVar(), null, ((CallStmt) stmt).getParams());
                    stmts.add(newCall);
                    registerCallStmt(newCall, ((CallStmt) stmt).getProcedure());
                } else {
                    stmts.add(stmt);
                }
            }
        } else {
            stmts = Collections.unmodifiableList(val.getStmts());
        }
        return new XCFA.Process.Procedure.Edge(
                transformed(builder, val.getSource()),
                transformed(builder, val.getTarget()),
                stmts
        );
    }

    protected XCFA.Process.Procedure.Location copy(XCFA.Process.Procedure.Builder builder, XCFA.Process.Procedure.Location val) {
        return new XCFA.Process.Procedure.Location(val.getName(), val.getDictionary());
    }

    protected XCFA.Process copy(XCFA.Builder _builder, XCFA.Process val) {
        var builder = XCFA.Process.builder();
        val.getProcedures().forEach(
                p -> builder.addProcedure(transformed(builder, p))
        );
        val.getParams().forEach(
                p -> builder.createVar(transformed(builder, p))
        );
        val.getThreadLocalVars().forEach(builder::createVar);
        builder.setMainProcedure(transformed(builder, val.getMainProcedure()));
        builder.setName(val.getName());
        return builder.build();
    }

    protected XCFA.Process.Procedure copy(XCFA.Process.Builder _builder, XCFA.Process.Procedure val) {
        var builder = XCFA.Process.Procedure.builder();
        val.getLocs().forEach(
                p -> builder.addLoc(transformed(builder, p))
        );
        val.getLocalVars().forEach(builder::createVar);
        val.getEdges().forEach(
                p -> builder.addEdge(transformed(builder, p))
        );
        val.getParams().forEach(
                p -> builder.createParam(transformed(builder, p))
        );
        builder.setRtype(val.getRtype());
        builder.setInitLoc(transformed(builder, val.getInitLoc()));
        if (val.getErrorLoc() != null)
            builder.setErrorLoc(transformed(builder, val.getErrorLoc()));
        builder.setFinalLoc(transformed(builder, val.getFinalLoc()));
        builder.setName(val.getName());
        return builder.build();
    }

    protected <TypeDecl extends Type> VarDecl<TypeDecl> copy(Object builder, VarDecl<TypeDecl> val) {
        return val;
    }

    /**
     * For post-processing a build. For example, adding new processes or variables.
     * @param builder
     */
    protected void beforeBuild(XCFA.Builder builder) {
        // Intentionally empty.
    }
}
