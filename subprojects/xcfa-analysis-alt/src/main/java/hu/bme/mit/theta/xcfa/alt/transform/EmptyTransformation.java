package hu.bme.mit.theta.xcfa.alt.transform;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

class EmptyTransformation {
    protected final XCFA old;

    private Map<Object, Object> cache = new HashMap<>();

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

    protected void afterBuild(XCFA xcfa) {
        //
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

    protected XCFA.Process.Procedure.Edge copy(XCFA.Process.Procedure.Builder builder, XCFA.Process.Procedure.Edge val) {
        return new XCFA.Process.Procedure.Edge(
                transformed(builder, val.getSource()),
                transformed(builder, val.getTarget()),
                Collections.unmodifiableList(val.getStmts())
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
        return Decls.Var(val.getName(), val.getType());
    }

    /**
     * For post-processing a build. For example, adding new processes
     * @param builder
     */
    protected void beforeBuild(XCFA.Builder builder) {

    }
}
