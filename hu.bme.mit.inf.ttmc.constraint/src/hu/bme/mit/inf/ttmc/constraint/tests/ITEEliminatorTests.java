package hu.bme.mit.inf.ttmc.constraint.tests;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.factory.DeclFactory;
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.constraint.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.iteelimin.IteToImpliyVisitor;

public class ITEEliminatorTests {
	// Manager and factories
	private ConstraintManager manager;
	private ExprFactory eFact;
	private DeclFactory dFact;
	private TypeFactory tFact;
	// Constants for testing
	private ConstDecl<BoolType> cA;
	private ConstDecl<BoolType> cB;
	private ConstDecl<BoolType> cC;
	private ConstDecl<BoolType> cD;
	private ConstDecl<BoolType> cE;
	// Transformator
	IteToImpliyVisitor visitor;
	
	@Before
	public void before(){
		// Create manager and get factories
		manager = new ConstraintManagerImpl();
		eFact = manager.getExprFactory();
		dFact = manager.getDeclFactory();
		tFact = manager.getTypeFactory();
		// Create constants
		cA = dFact.Const("A", tFact.Bool());
		cB = dFact.Const("B", tFact.Bool());
		cC = dFact.Const("C", tFact.Bool());
		cD = dFact.Const("D", tFact.Bool());
		cE = dFact.Const("E", tFact.Bool());
		// Create transformator
		visitor = new IteToImpliyVisitor(manager);
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testSimple() {
		// ite(A,B,C)
		Assert.assertEquals(
			eFact.Ite(eFact.Ref(cA), eFact.Ref(cB), eFact.Ref(cC)).accept(visitor, null),
			eFact.And(eFact.Or(eFact.Not(eFact.Ref(cA)), eFact.Ref(cB)), eFact.Or(eFact.Ref(cA), eFact.Ref(cC)))
			);
		
		// ite(A,ite(B,C,D),E)
		Assert.assertEquals(
			eFact.Ite(eFact.Ref(cA), eFact.Ite(eFact.Ref(cB), eFact.Ref(cC), eFact.Ref(cD)), eFact.Ref(cE)).accept(visitor, null),
			eFact.And(
					eFact.Or(eFact.Not(eFact.Ref(cA)), eFact.And(
							eFact.Or(eFact.Not(eFact.Ref(cB)), eFact.Ref(cC)),
							eFact.Or(eFact.Ref(cB), eFact.Ref(cD)))),
					eFact.Or(eFact.Ref(cA), eFact.Ref(cE)))
			);
	}
}
