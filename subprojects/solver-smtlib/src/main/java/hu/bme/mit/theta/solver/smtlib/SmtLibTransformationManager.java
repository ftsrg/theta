package hu.bme.mit.theta.solver.smtlib;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;

public class SmtLibTransformationManager {
    private final SmtLibTypeTransformer typeTransformer;
    private final SmtLibDeclTransformer declTransformer;
    private final SmtLibExprTransformer exprTransformer;

    public SmtLibTransformationManager(final SmtLibSymbolTable symbolTable) {
        this.typeTransformer = instantiateTypeTransformer(this);
        this.declTransformer = instantiateDeclTransformer(this, symbolTable);
        this.exprTransformer = instantiateExprTransformer(this);
    }

    public final String toSort(final Type type) {
        return typeTransformer.toSort(type);
    }

    public final String toSymbol(final Decl<?> decl) {
        return declTransformer.toSymbol(decl);
    }

    public final String toTerm(final Expr<?> expr) {
        return exprTransformer.toTerm(expr);
    }

    protected SmtLibTypeTransformer instantiateTypeTransformer(final SmtLibTransformationManager transformer) {
        return new SmtLibTypeTransformer(transformer);
    }

    protected SmtLibDeclTransformer instantiateDeclTransformer(
        final SmtLibTransformationManager transformer, final SmtLibSymbolTable symbolTable
    ) {
        return new SmtLibDeclTransformer(transformer, symbolTable);
    }

    protected SmtLibExprTransformer instantiateExprTransformer(final SmtLibTransformationManager transformer) {
        return new SmtLibExprTransformer(transformer);
    }
}
