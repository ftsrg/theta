package hu.bme.mit.inf.ttmc.aiger.impl.elements;

import java.util.List;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;

public final class InVar extends HWElement {
	private final VarDecl<BoolType> varDecl;
	
	public InVar(int nr, String token, STSManager manager) {
		this(nr, Integer.parseInt(token), manager);
	}

	public InVar(int nr, int literal, STSManager manager) {
		super(literal/2);
		varDecl = manager.getDeclFactory().Var("I" + nr + "_l" + varId, manager.getTypeFactory().Bool());
	}

	@Override
	public Expr<? extends BoolType> getExpr(STSManager manager, List<HWElement> elements) {
		return varDecl.getRef();
	}

}
