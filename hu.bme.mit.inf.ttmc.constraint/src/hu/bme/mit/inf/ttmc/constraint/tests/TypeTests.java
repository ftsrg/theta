package hu.bme.mit.inf.ttmc.constraint.tests;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.constraint.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;

public class TypeTests {

	@Test
	public final void testIsLeq() {
		final ConstraintManager manager = new ConstraintManagerImpl();
		final TypeFactory tf = manager.getTypeFactory();

		final BoolType Bool = tf.Bool();
		final IntType Int = tf.Int();
		final RatType Rat = tf.Rat();
		final FuncType<IntType, RatType> IntToRat = tf.Func(Int, Rat);
		final FuncType<IntType, IntType> IntToInt = tf.Func(Int, Int);
		final FuncType<RatType, RatType> RatToRat = tf.Func(Rat, Rat);
		final FuncType<RatType, IntType> RatToInt = tf.Func(Rat, Int);

		assertTrue(Bool.isLeq(Bool));
		assertTrue(Int.isLeq(Int));
		assertTrue(Int.isLeq(Rat));
		assertTrue(Rat.isLeq(Rat));

		assertTrue(RatToInt.isLeq(RatToInt));
		assertTrue(RatToInt.isLeq(RatToRat));
		assertTrue(RatToInt.isLeq(IntToInt));
		assertTrue(RatToInt.isLeq(IntToRat));

		assertTrue(RatToRat.isLeq(RatToRat));
		assertTrue(RatToRat.isLeq(IntToRat));

		assertTrue(IntToInt.isLeq(IntToInt));
		assertTrue(IntToInt.isLeq(IntToRat));

		assertTrue(IntToRat.isLeq(IntToRat));

		////

		assertFalse(Bool.isLeq(Int));
		assertFalse(Bool.isLeq(Rat));
		assertFalse(Int.isLeq(Bool));
		assertFalse(Rat.isLeq(Bool));
		assertFalse(Rat.isLeq(Int));

		assertFalse(RatToInt.isLeq(Bool));
		assertFalse(RatToInt.isLeq(Int));
		assertFalse(RatToInt.isLeq(Rat));

		assertFalse(RatToRat.isLeq(RatToInt));
		assertFalse(RatToRat.isLeq(IntToInt));

		assertFalse(IntToInt.isLeq(RatToInt));
		assertFalse(IntToInt.isLeq(RatToRat));

		assertFalse(IntToRat.isLeq(RatToInt));
		assertFalse(IntToRat.isLeq(IntToInt));
		assertFalse(IntToRat.isLeq(RatToRat));
	}

}
