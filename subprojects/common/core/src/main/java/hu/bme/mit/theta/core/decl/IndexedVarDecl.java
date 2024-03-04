package hu.bme.mit.theta.core.decl;

import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;

public class IndexedVarDecl<DeclType extends Type> extends VarDecl<DeclType> {

    private final VarDecl<DeclType> original;
    private final RefExpr<DeclType> constRef;

    IndexedVarDecl(final String name, final VarDecl<DeclType> original) {
        super(name, original.getType());
        this.original = original;
        this.constRef = RefExpr.of(Decls.Const(name, original.getType()));
    }

    public static <DeclType extends Type> IndexedVarDecl<DeclType> of(final String name, final VarDecl<DeclType> original) {
        return new IndexedVarDecl<>(name, original);
    }

    public VarDecl<DeclType> getOriginal() {
        return original;
    }

    public RefExpr<DeclType> getConstRef() {
        return constRef;
    }
}
