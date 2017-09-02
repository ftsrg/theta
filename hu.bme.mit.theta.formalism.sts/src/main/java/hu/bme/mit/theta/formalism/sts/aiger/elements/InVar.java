package hu.bme.mit.theta.formalism.sts.aiger.elements;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

import java.util.List;

import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class InVar extends HwElement {
	private final VarDecl<BoolType> varDecl;

	public InVar(final int nr, final String token) {
		this(nr, Integer.parseInt(token));
	}

	public InVar(final int nr, final int literal) {
		super(literal / 2);
		varDecl = Decls.Var("I" + nr + "_l" + varId, Bool());
	}

	@Override
	public Expr<BoolType> getExpr(final List<HwElement> elements) {
		return varDecl.getRef();
	}

}
