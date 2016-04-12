package hu.bme.mit.inf.ttmc.core.tests;

import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.inf.ttmc.core.ConstraintManager;
import hu.bme.mit.inf.ttmc.core.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.core.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.FuncType;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.core.type.RatType;
import hu.bme.mit.inf.ttmc.core.type.Type;

@RunWith(Parameterized.class)
public class TypeIsLeqTests {

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
		final ConstraintManager manager = new ConstraintManagerImpl();
		final TypeFactory tf = manager.getTypeFactory();

		BOOL = tf.Bool();
		INT = tf.Int();
		RAT = tf.Rat();
		INT_TO_RAT = tf.Func(INT, RAT);
		INT_TO_INT = tf.Func(INT, INT);
		RAT_TO_RAT = tf.Func(RAT, RAT);
		RAT_TO_INT = tf.Func(RAT, INT);
	}

	@Test
	public final void testIsLeq() {
		assertEquals(type1.isLeq(type2), expected);
	}

}
