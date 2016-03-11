package hu.bme.mit.inf.ttmc.aiger.elements;

import java.util.List;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;

public final class InVar extends HWElement {
	private final VarDecl<BoolType> varDecl;
	
	public InVar(String token, STSManager manager) {
		this(Integer.parseInt(token), manager);
	}

	public InVar(int literal, STSManager manager) {
		super(literal/2);
		varDecl = manager.getDeclFactory().Var("v" + varId, manager.getTypeFactory().Bool());
	}

	@Override
	public Expr<? extends BoolType> getExpr(STSManager manager, List<HWElement> elements) {
		return varDecl.getRef();
	}

}
