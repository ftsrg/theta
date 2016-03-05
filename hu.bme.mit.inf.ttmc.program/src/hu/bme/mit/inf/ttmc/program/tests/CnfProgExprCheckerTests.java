package hu.bme.mit.inf.ttmc.program.tests;

import org.junit.Before;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.constraint.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.program.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.program.factory.ProgramFactory;
import hu.bme.mit.inf.ttmc.program.factory.ProgramFactoryImpl;
import hu.bme.mit.inf.ttmc.program.utils.impl.CnfProgExprChecker;
import org.junit.Assert;

public class CnfProgExprCheckerTests {
	// Manager and factories
		private ConstraintManager manager;
		private ExprFactory efc;
		private TypeFactory tfc;
		private ProgramFactory pfc;
		// Constants and variaBles for testing
		private VarRefExpr<BoolType> vA, vB, vC;
		// CNF checker
		CnfProgExprChecker cnfChecker;
		
		@Before
		public void Before() {
			// Create manager and get factories
			manager = new ConstraintManagerImpl();
			efc = manager.getExprFactory();
			tfc = manager.getTypeFactory();
			pfc = new ProgramFactoryImpl();
			// Create constants and variaBles
			vA = pfc.Ref(pfc.Var("A", tfc.Bool()));
			vB = pfc.Ref(pfc.Var("B", tfc.Bool()));
			vC = pfc.Ref(pfc.Var("C", tfc.Bool()));
			// Create CNF checker
			cnfChecker = new CnfProgExprChecker();
		}
		
		@SuppressWarnings("unchecked")
		@Test
		public void testCnfProgExprCheckerTrue() {
			// A
			Assert.assertTrue(cnfChecker.isExprInCnf(vA));
			// A'
			Assert.assertTrue(cnfChecker.isExprInCnf(pfc.Prime(vA)));
			// !A
			Assert.assertTrue(cnfChecker.isExprInCnf(efc.Not(vA)));
			// !(A')
			Assert.assertTrue(cnfChecker.isExprInCnf(efc.Not(pfc.Prime(vA))));
			// !A or B' or !C
			Assert.assertTrue(cnfChecker.isExprInCnf(efc.Or(efc.Not(vA), pfc.Prime(vB), efc.Not(vC))));
			// !A and B' and !C
			Assert.assertTrue(cnfChecker.isExprInCnf(efc.And(efc.Not(vA), pfc.Prime(vB), efc.Not(vC))));
			// !A and (B and !C)
			Assert.assertTrue(cnfChecker.isExprInCnf(efc.And(efc.Not(vA), efc.And(vB, efc.Not(vC)))));
			// !A and (B' or !C)
			Assert.assertTrue(cnfChecker.isExprInCnf(efc.And(efc.Not(vA), efc.Or(pfc.Prime(vB), efc.Not(vC)))));
		}
		
		@SuppressWarnings("unchecked")
		@Test
		public void testCnfProgExprCheckerFalse() {
			// !!A
			Assert.assertFalse(cnfChecker.isExprInCnf(efc.Not(efc.Not(vA))));
			// !A and B and !C
			Assert.assertTrue(cnfChecker.isExprInCnf(efc.And(efc.Not(vA), vB, efc.Not(vC))));
			// !A or (B and !C)
			Assert.assertFalse(cnfChecker.isExprInCnf(efc.Or(efc.Not(vA), efc.And(vB, efc.Not(vC)))));
			// !(A and B)
			Assert.assertFalse(cnfChecker.isExprInCnf(efc.Not(efc.And(vA, vB))));
			// !(A or B)
			Assert.assertFalse(cnfChecker.isExprInCnf(efc.Not(efc.Or(vA, vB))));
			// A -> B
			Assert.assertFalse(cnfChecker.isExprInCnf(efc.Imply(vA, vB)));
			// A <-> B
			Assert.assertFalse(cnfChecker.isExprInCnf(efc.Iff(vA, vB)));
			// (!A)'
			Assert.assertFalse(cnfChecker.isExprInCnf(efc.Not(efc.Not(vA))));
			// (A and B)'
			Assert.assertFalse(cnfChecker.isExprInCnf(pfc.Prime(efc.And(vA, vB))));
			// (A or B)'
			Assert.assertFalse(cnfChecker.isExprInCnf(pfc.Prime(efc.Or(vA, vB))));
		}
}
