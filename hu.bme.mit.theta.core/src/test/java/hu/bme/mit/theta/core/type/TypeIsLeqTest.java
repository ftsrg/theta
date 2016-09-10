package hu.bme.mit.theta.core.type;

import static hu.bme.mit.theta.core.type.impl.Types.Bool;
import static hu.bme.mit.theta.core.type.impl.Types.Func;
import static hu.bme.mit.theta.core.type.impl.Types.Int;
import static hu.bme.mit.theta.core.type.impl.Types.Rat;
import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.FuncType;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.core.type.Type;

@RunWith(Parameterized.class)
public class TypeIsLeqTest {

	private static final BoolType BOOL;
	private static final IntType INT;
	private static final RatType RAT;
	private static final FuncType<IntType, RatType> INT_TO_RAT;
	private static final FuncType<IntType, IntType> INT_TO_INT;
	private static final FuncType<RatType, RatType> RAT_TO_RAT;
	private static final FuncType<RatType, IntType> RAT_TO_INT;

	@Parameter(value = 0)
	public Type type1;

	@Parameter(value = 1)
	public Type type2;

	@Parameter(value = 2)
	public boolean expected;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ BOOL, BOOL, true },

				{ BOOL, INT, false },

				{ BOOL, RAT, false },

				{ INT, BOOL, false },

				{ INT, INT, true },

				{ INT, RAT, true },

				{ RAT, BOOL, false },

				{ RAT, INT, false },

				{ RAT, RAT, true },

				{ RAT_TO_INT, BOOL, false },

				{ RAT_TO_INT, INT, false },

				{ RAT_TO_INT, RAT, false },

				{ RAT_TO_INT, RAT_TO_INT, true },

				{ RAT_TO_INT, INT_TO_INT, true },

				{ RAT_TO_INT, RAT_TO_RAT, true },

				{ RAT_TO_INT, INT_TO_RAT, true },

				{ INT_TO_INT, RAT_TO_INT, false },

				{ INT_TO_INT, INT_TO_INT, true },

				{ INT_TO_INT, RAT_TO_RAT, false },

				{ INT_TO_INT, INT_TO_RAT, true },

				{ RAT_TO_RAT, RAT_TO_INT, false },

				{ RAT_TO_RAT, INT_TO_INT, false },

				{ RAT_TO_RAT, RAT_TO_RAT, true },

				{ RAT_TO_RAT, INT_TO_RAT, true },

				{ INT_TO_RAT, RAT_TO_INT, false },

				{ INT_TO_RAT, INT_TO_INT, false },

				{ INT_TO_RAT, RAT_TO_RAT, false },

				{ INT_TO_RAT, INT_TO_RAT, true },

		});
	}

	static {
		BOOL = Bool();
		INT = Int();
		RAT = Rat();
		INT_TO_RAT = Func(Int(), Rat());
		INT_TO_INT = Func(Int(), Int());
		RAT_TO_RAT = Func(Rat(), Rat());
		RAT_TO_INT = Func(Rat(), Int());
	}

	@Test
	public final void testIsLeq() {
		assertEquals(type1.isLeq(type2), expected);
	}

}
