package hu.bme.mit.inf.ttmc.aiger.impl.elements;

import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Iff;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Not;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Bool;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Var;
import static hu.bme.mit.inf.ttmc.formalism.common.expr.impl.Exprs2.Prime;
import static hu.bme.mit.inf.ttmc.formalism.common.expr.impl.Exprs2.Ref;

import java.util.List;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

public final class Latch extends HWElement {
	private final int nextState;
	private final VarDecl<BoolType> varDecl;

	public Latch(final int nr, final String[] tokens) {
		this(nr, Integer.parseInt(tokens[0]), Integer.parseInt(tokens[1]));
	}

	public Latch(final int nr, final int actualState, final int nextState) {
		super(actualState / 2);
		this.nextState = nextState;
		varDecl = Var("L" + nr + "_l" + varId, Bool());
	}

	@Override
	public Expr<? extends BoolType> getExpr(final List<HWElement> elements) {
		return Ref(varDecl);
	}

	public Expr<? extends BoolType> getInitExpr() {
		return Not(Ref(varDecl));
	}

	public Expr<? extends BoolType> getTransExpr(final List<HWElement> elements) {
		Expr<? extends BoolType> expr = elements.get(nextState / 2).getExpr(elements);
		if (nextState % 2 == 1)
			expr = Not(expr);
		return Iff(Prime(Ref(varDecl)), expr);
	}

}
