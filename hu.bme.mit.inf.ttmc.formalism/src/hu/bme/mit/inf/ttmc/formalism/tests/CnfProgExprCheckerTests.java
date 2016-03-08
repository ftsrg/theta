package hu.bme.mit.inf.ttmc.formalism.tests;

import org.junit.Before;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.constraint.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.factory.ProgramFactory;
import hu.bme.mit.inf.ttmc.formalism.factory.ProgramFactoryImpl;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.CNFFormalismExprChecker;

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
		CNFFormalismExprChecker cnfChecker;
		
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
			cnfChecker = new CNFFormalismExprChecker();
		}
		
		@SuppressWarnings("unchecked")
		@Test
		public void testCnfProgExprCheckerTrue() {
			// A
			Assert.assertTrue(cnfChecker.isExprInCNF(vA));
			// A'
			Assert.assertTrue(cnfChecker.isExprInCNF(pfc.Prime(vA)));
			// !A
			Assert.assertTrue(cnfChecker.isExprInCNF(efc.Not(vA)));
			// !(A')
			Assert.assertTrue(cnfChecker.isExprInCNF(efc.Not(pfc.Prime(vA))));
			// !A or B' or !C
			Assert.assertTrue(cnfChecker.isExprInCNF(efc.Or(efc.Not(vA), pfc.Prime(vB), efc.Not(vC))));
			// !A and B' and !C
			Assert.assertTrue(cnfChecker.isExprInCNF(efc.And(efc.Not(vA), pfc.Prime(vB), efc.Not(vC))));
			// !A and (B and !C)
			Assert.assertTrue(cnfChecker.isExprInCNF(efc.And(efc.Not(vA), efc.And(vB, efc.Not(vC)))));
			// !A and (B' or !C)
			Assert.assertTrue(cnfChecker.isExprInCNF(efc.And(efc.Not(vA), efc.Or(pfc.Prime(vB), efc.Not(vC)))));
		}
		
		@SuppressWarnings("unchecked")
		@Test
		public void testCnfProgExprCheckerFalse() {
			// !!A
			Assert.assertFalse(cnfChecker.isExprInCNF(efc.Not(efc.Not(vA))));
			// !A and B and !C
			Assert.assertTrue(cnfChecker.isExprInCNF(efc.And(efc.Not(vA), vB, efc.Not(vC))));
			// !A or (B and !C)
			Assert.assertFalse(cnfChecker.isExprInCNF(efc.Or(efc.Not(vA), efc.And(vB, efc.Not(vC)))));
			// !(A and B)
			Assert.assertFalse(cnfChecker.isExprInCNF(efc.Not(efc.And(vA, vB))));
			// !(A or B)
			Assert.assertFalse(cnfChecker.isExprInCNF(efc.Not(efc.Or(vA, vB))));
			// A -> B
			Assert.assertFalse(cnfChecker.isExprInCNF(efc.Imply(vA, vB)));
			// A <-> B
			Assert.assertFalse(cnfChecker.isExprInCNF(efc.Iff(vA, vB)));
			// (!A)'
			Assert.assertFalse(cnfChecker.isExprInCNF(efc.Not(efc.Not(vA))));
			// (A and B)'
			Assert.assertFalse(cnfChecker.isExprInCNF(pfc.Prime(efc.And(vA, vB))));
			// (A or B)'
			Assert.assertFalse(cnfChecker.isExprInCNF(pfc.Prime(efc.Or(vA, vB))));
		}
}
