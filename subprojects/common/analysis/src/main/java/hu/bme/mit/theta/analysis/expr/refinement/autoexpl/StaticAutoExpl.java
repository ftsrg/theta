package hu.bme.mit.theta.analysis.expr.refinement.autoexpl;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.Set;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

public class StaticAutoExpl implements AutoExpl{

    private final Set<VarDecl<?>> ctrlVars;

    public StaticAutoExpl(final Set<VarDecl<?>> ctrlVars){
        this.ctrlVars = ctrlVars;
    }

    @Override
    public boolean isExpl(final VarDecl<?> decl) {
        return ctrlVars.contains(decl) || decl.getType() == Bool();
    }

    @Override
    public void update(final Expr<BoolType> itp) {}
}
