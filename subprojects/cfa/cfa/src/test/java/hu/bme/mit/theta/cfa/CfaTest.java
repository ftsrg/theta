package hu.bme.mit.theta.cfa;

import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmts;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntType;
import org.junit.Test;

public class CfaTest {

    @Test(expected = IllegalArgumentException.class)
    public void testDuplicateLocationName() {
        CFA.Builder builder = CFA.builder();
        builder.createLoc("A");
        builder.createLoc("B");
        builder.createLoc("A");
    }

    @Test(expected = IllegalArgumentException.class)
    public void testDuplicateVarName() {
        CFA.Builder builder = CFA.builder();
        VarDecl<IntType> v1 = Decls.Var("x", IntExprs.Int());
        VarDecl<IntType> v2 = Decls.Var("x", IntExprs.Int());
        CFA.Loc init = builder.createLoc();
        CFA.Loc loc1 = builder.createLoc();
        CFA.Loc loc2 = builder.createLoc();
        builder.createEdge(init, loc1, Stmts.Havoc(v1));
        builder.createEdge(init, loc2, Stmts.Havoc(v2));
        builder.setInitLoc(init);
        builder.build();
    }
}
