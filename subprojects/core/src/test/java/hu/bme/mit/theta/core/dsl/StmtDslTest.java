package hu.bme.mit.theta.core.dsl;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntType;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;
import static hu.bme.mit.theta.core.stmt.Stmts.*;

@RunWith(Parameterized.class)
public class StmtDslTest {
    @Parameterized.Parameter(value = 0)
    public String actual;

    @Parameterized.Parameter(value = 1)
    public Stmt expected;

    @Parameterized.Parameter(value = 2)
    public Collection<Decl<?>> decls;

    private static VarDecl<IntType> x = Decls.Var("x", IntExprs.Int());

    @Parameterized.Parameters
    public static Collection<Object[]> data() {
        return Arrays.asList(new Object[][]{

                {"assume true", Assume(True()), null},

                {"x := x + 1", Assign(x, Add(x.getRef(), Int(1))) , Collections.singleton(x)},

                {"havoc x", Havoc(x) , Collections.singleton(x)}

        });
    }

    @Test
    public void test() {
        final CoreDslManager manager = new CoreDslManager();

        if (decls != null) {
            decls.forEach(decl -> manager.declare(decl));
        }

        Assert.assertEquals(expected, manager.parseStmt(actual));
    }
}
