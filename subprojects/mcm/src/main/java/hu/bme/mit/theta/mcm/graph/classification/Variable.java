package hu.bme.mit.theta.mcm.graph.classification;

import hu.bme.mit.theta.core.decl.VarDecl;

public class Variable {
    private final VarDecl<?> varDecl;

    public Variable(VarDecl<?> varDecl) {
        this.varDecl = varDecl;
    }

    @Override
    public String toString() {
        return varDecl.getName();
    }
}
