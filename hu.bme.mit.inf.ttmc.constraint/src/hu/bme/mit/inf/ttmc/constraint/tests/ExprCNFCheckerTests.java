package hu.bme.mit.inf.ttmc.constraint.tests;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.constraint.factory.DeclFactory;
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.constraint.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ExprUtils;

public class ExprCNFCheckerTests {
	// Manager and factories
		private ConstraintManager manager;
		private ExprFactory efc;
		private DeclFactory dfc;
		private TypeFactory tfc;
		// Constants for testing
		private ConstRefExpr<BoolType> cA, cB, cC;
		
		@Before
		public void before(){
			// Create manager and get factories
			manager = new ConstraintManagerImpl();
			efc = manager.getExprFactory();
			dfc = manager.getDeclFactory();
			tfc = manager.getTypeFactory();
			// Create constants
			cA = dfc.Const("A", tfc.Bool()).getRef();
			cB = dfc.Const("B", tfc.Bool()).getRef();
			cC = dfc.Const("C", tfc.Bool()).getRef();
		}
		
		@SuppressWarnings("unchecked")
		@Test
		public void testCnfCheckerTrue() {
			// A
			Assert.assertTrue(ExprUtils.isExprCNF(cA));
			// !A
			Assert.assertTrue(ExprUtils.isExprCNF(efc.Not(cA)));
			// !A or B or !C
			Assert.assertTrue(ExprUtils.isExprCNF(efc.Or(efc.Not(cA), cB, efc.Not(cC))));
			// !A and B and !C
			Assert.assertTrue(ExprUtils.isExprCNF(efc.And(efc.Not(cA), cB, efc.Not(cC))));
			// !A and (B and !C)
			Assert.assertTrue(ExprUtils.isExprCNF(efc.And(efc.Not(cA), efc.And(cB, efc.Not(cC)))));
			// !A and (B or !C)
			Assert.assertTrue(ExprUtils.isExprCNF(efc.And(efc.Not(cA), efc.Or(cB, efc.Not(cC)))));
		}
		

		@SuppressWarnings("unchecked")
		@Test
		public void testCnfCheckerFalse() {
			// !!A
			Assert.assertFalse(ExprUtils.isExprCNF(efc.Not(efc.Not(cA))));
			// !A and B and !C
			Assert.assertTrue(ExprUtils.isExprCNF(efc.And(efc.Not(cA), cB, efc.Not(cC))));
			// !A or (B and !C)
			Assert.assertFalse(ExprUtils.isExprCNF(efc.Or(efc.Not(cA), efc.And(cB, efc.Not(cC)))));
			// !(A and B)
			Assert.assertFalse(ExprUtils.isExprCNF(efc.Not(efc.And(cA, cB))));
			// !(A or B)
			Assert.assertFalse(ExprUtils.isExprCNF(efc.Not(efc.Or(cA, cB))));
			// A -> B
			Assert.assertFalse(ExprUtils.isExprCNF(efc.Imply(cA, cB)));
			// A <-> B
			Assert.assertFalse(ExprUtils.isExprCNF(efc.Iff(cA, cB)));
		}
}
