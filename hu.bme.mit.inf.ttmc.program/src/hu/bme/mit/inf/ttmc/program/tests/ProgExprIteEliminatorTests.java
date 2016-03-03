package hu.bme.mit.inf.ttmc.program.tests;

import org.junit.Assert;
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
import hu.bme.mit.inf.ttmc.program.utils.impl.ProgExprIteEliminator;

public class ProgExprIteEliminatorTests {
	// Manager and factories
	private ConstraintManager manager;
	private ExprFactory efc;
	private TypeFactory tfc;
	private ProgramFactory pfc;
	// Constants and variables for testing
	private VarRefExpr<BoolType> vA, vB, vC;
	// Transformator
	ProgExprIteEliminator eliminator;
	
	@Before
	public void before() {
		// Create manager and get factories
		manager = new ConstraintManagerImpl();
		efc = manager.getExprFactory();
		tfc = manager.getTypeFactory();
		pfc = new ProgramFactoryImpl();
		// Create constants and variables
		vA = pfc.Ref(pfc.Var("A", tfc.Bool()));
		vB = pfc.Ref(pfc.Var("B", tfc.Bool()));
		vC = pfc.Ref(pfc.Var("C", tfc.Bool()));
		// Create transformator
		eliminator = new ProgExprIteEliminator(manager);
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testProgExprIteEliminator() {
		// if A then B else C
		Assert.assertEquals(
				eliminator.eliminate(efc.Ite(vA, vB, vC)),
				efc.And(efc.Or(efc.Not(vA), vB), efc.Or(vA, vC))
				);
		// (if A then B else C)'
		Assert.assertEquals(
				eliminator.eliminate(pfc.Prime(efc.Ite(vA, vB, vC))),
				efc.And(efc.Or(efc.Not(vA), pfc.Prime(vB)), efc.Or(vA, pfc.Prime(vC)))
				);
	}
}
