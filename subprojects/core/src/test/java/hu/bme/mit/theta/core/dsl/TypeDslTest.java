package hu.bme.mit.theta.core.dsl;

import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.rattype.RatExprs;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.util.Arrays;
import java.util.Collection;

@RunWith(Parameterized.class)
public class TypeDslTest {

    @Parameterized.Parameter(value = 0)
    public String actual;

    @Parameterized.Parameter(value = 1)
    public Type expected;


    @Parameterized.Parameters
    public static Collection<Object[]> data() {
        return Arrays.asList(new Object[][]{

                {"int", IntExprs.Int()},

                {"rat", RatExprs.Rat()},

                {"bool", BoolExprs.Bool()},

                {"[int] -> bool", ArrayExprs.Array(IntExprs.Int(), BoolExprs.Bool())},

                {"[bool] -> rat", ArrayExprs.Array(BoolExprs.Bool(), RatExprs.Rat())},

                {"[bool] -> [int] -> rat",
                        ArrayExprs.Array(BoolExprs.Bool(), ArrayExprs.Array(IntExprs.Int(), RatExprs.Rat()))},

                {"[[bool] -> int] -> rat",
                        ArrayExprs.Array(ArrayExprs.Array(BoolExprs.Bool(), IntExprs.Int()), RatExprs.Rat())},

        });
    }

    @Test
    public void test() {
        final CoreDslManager manager = new CoreDslManager();
        Assert.assertEquals(expected, manager.parseType(actual));
    }
}
