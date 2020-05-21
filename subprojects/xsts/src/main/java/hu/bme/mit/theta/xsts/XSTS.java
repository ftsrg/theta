package hu.bme.mit.theta.xsts;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.stmt.SequenceStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.xsts.dsl.TypeDecl;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import static com.google.common.base.Preconditions.checkNotNull;

public final class XSTS {
    private final Collection<VarDecl<?>> vars;
    private final Collection<TypeDecl> types;
    private final NonDetStmt transitions;
    private final NonDetStmt envAction;
    private final NonDetStmt initAction;

    private final Expr<BoolType> initFormula;
    private final Expr<BoolType> prop;

    public NonDetStmt getInitAction() { return initAction; }

    public Collection<VarDecl<?>> getVars() {
        return vars;
    }

    public Collection<TypeDecl> getTypes() {
        return types;
    }

    public Expr<BoolType> getProp() { return prop; }

    public NonDetStmt getTransitions() {
        return transitions;
    }

    public Expr<BoolType> getInitFormula() { return initFormula; }

    public NonDetStmt getEnvAction() {
        return envAction;
    }

    public XSTS(final Collection<TypeDecl> types, final NonDetStmt initAction,final NonDetStmt transitions, final NonDetStmt envAction, final Expr<BoolType> initFormula, final Expr<BoolType> prop) {
        this.transitions = checkNotNull(transitions);
        this.initFormula = checkNotNull(initFormula);
        this.envAction = checkNotNull(envAction);
        this.prop = checkNotNull(prop);
        this.initAction = checkNotNull(initAction);
        this.types=types;
        final Set<VarDecl<?>> tmpVars = new HashSet<>();
        tmpVars.addAll(StmtUtils.getVars(transitions));
        tmpVars.addAll(StmtUtils.getVars(envAction));
        tmpVars.addAll(StmtUtils.getVars(initAction));
        tmpVars.addAll(ExprUtils.getVars(initFormula));
        tmpVars.addAll(ExprUtils.getVars(prop));
        this.vars = Collections.unmodifiableCollection(tmpVars);
    }

}
