package hu.bme.mit.inf.ttmc.constraint.z3.expr;

import java.util.Collection;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.ExistsExprImpl;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.z3.decl.Z3Decl;

public class Z3ExistsExpr extends ExistsExprImpl implements Z3Expr<BoolType> {

	private final Context context;
	
	private volatile com.microsoft.z3.Quantifier term;
	
	public Z3ExistsExpr(final Collection<? extends ParamDecl<? extends Type>> paramDecls,
			final Expr<? extends BoolType> op, final Context context) {
		super(paramDecls, op);
		this.context = context;
	}

	@Override
	public com.microsoft.z3.Quantifier getTerm() {
		if (term == null) {
			final Z3Expr<?> op = (Z3Expr<?>) getOp();
			final com.microsoft.z3.BoolExpr opTerm = (com.microsoft.z3.BoolExpr) op.getTerm();
			
			final com.microsoft.z3.Expr[] paramTerms = new com.microsoft.z3.Expr[getParamDecls().size()];
			int i = 0;
			for (ParamDecl<?> paramDecl : getParamDecls()) {
				final Z3Decl<?> z3ParamDecl = (Z3Decl<?>) paramDecl;
				final com.microsoft.z3.FuncDecl paramSymbol = z3ParamDecl.getSymbol();
				paramTerms[i] = context.mkConst(paramSymbol);
				i++;
			}
			term = context.mkExists(paramTerms, opTerm, 1, null, null, null, null);
		}
		return term;
	}

}
