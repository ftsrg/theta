package hu.bme.mit.inf.ttmc.formalism.tests;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.constraint.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.factory.VarDeclFactory;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.factory.STSExprFactory;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSManagerImpl;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils;

public class FormalismExprCNFCheckerTests {
	// Factories
	private VarDeclFactory dfc;
	private TypeFactory tfc;
	private STSExprFactory efc;
	// Constants and variaBles for testing
	private VarRefExpr<BoolType> vA, vB, vC;
	
	@Before
	public void Before() {
		// Create manager and get factories
		STSManager manager = new STSManagerImpl(new ConstraintManagerImpl());
		dfc = manager.getDeclFactory();
		efc = manager.getExprFactory();
		tfc = manager.getTypeFactory();
		// Create constants and variaBles
		vA = dfc.Var("A", tfc.Bool()).getRef();
		vB = dfc.Var("B", tfc.Bool()).getRef();
		vC = dfc.Var("C", tfc.Bool()).getRef();
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testCnfProgExprCheckerTrue() {
		// A
		Assert.assertTrue(FormalismUtils.isExprCNF(vA));
		// A'
		Assert.assertTrue(FormalismUtils.isExprCNF(efc.Prime(vA)));
		// !A
		Assert.assertTrue(FormalismUtils.isExprCNF(efc.Not(vA)));
		// !(A')
		Assert.assertTrue(FormalismUtils.isExprCNF(efc.Not(efc.Prime(vA))));
		// !A or B' or !C
		Assert.assertTrue(FormalismUtils.isExprCNF(efc.Or(efc.Not(vA), efc.Prime(vB), efc.Not(vC))));
		// !A and B' and !C
		Assert.assertTrue(FormalismUtils.isExprCNF(efc.And(efc.Not(vA), efc.Prime(vB), efc.Not(vC))));
		// !A and (B and !C)
		Assert.assertTrue(FormalismUtils.isExprCNF(efc.And(efc.Not(vA), efc.And(vB, efc.Not(vC)))));
		// !A and (B' or !C)
		Assert.assertTrue(FormalismUtils.isExprCNF(efc.And(efc.Not(vA), efc.Or(efc.Prime(vB), efc.Not(vC)))));
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testCnfProgExprCheckerFalse() {
		// !!A
		Assert.assertFalse(FormalismUtils.isExprCNF(efc.Not(efc.Not(vA))));
		// !A and B and !C
		Assert.assertTrue(FormalismUtils.isExprCNF(efc.And(efc.Not(vA), vB, efc.Not(vC))));
		// !A or (B and !C)
		Assert.assertFalse(FormalismUtils.isExprCNF(efc.Or(efc.Not(vA), efc.And(vB, efc.Not(vC)))));
		// !(A and B)
		Assert.assertFalse(FormalismUtils.isExprCNF(efc.Not(efc.And(vA, vB))));
		// !(A or B)
		Assert.assertFalse(FormalismUtils.isExprCNF(efc.Not(efc.Or(vA, vB))));
		// A -> B
		Assert.assertFalse(FormalismUtils.isExprCNF(efc.Imply(vA, vB)));
		// A <-> B
		Assert.assertFalse(FormalismUtils.isExprCNF(efc.Iff(vA, vB)));
		// (!A)'
		Assert.assertFalse(FormalismUtils.isExprCNF(efc.Not(efc.Not(vA))));
		// (A and B)'
		Assert.assertFalse(FormalismUtils.isExprCNF(efc.Prime(efc.And(vA, vB))));
		// (A or B)'
		Assert.assertFalse(FormalismUtils.isExprCNF(efc.Prime(efc.Or(vA, vB))));
	}
}
