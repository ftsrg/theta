package hu.bme.mit.inf.ttmc.constraint.z3.expr;

import com.microsoft.z3.Context;
import com.microsoft.z3.FuncDecl;

import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.ConstRefExprImpl;
import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.z3.decl.Z3ConstDecl;

public class Z3ConstRefExpr<DeclType extends Type> extends ConstRefExprImpl<DeclType> implements Z3Expr<DeclType> {

	private final Context context;

	private volatile com.microsoft.z3.Expr term;

	public Z3ConstRefExpr(ConstDecl<DeclType> constDecl, final Context context) {
		super(constDecl);
		this.context = context;
	}

	@Override
	public com.microsoft.z3.Expr getTerm() {
		if (getDecl().getType() instanceof FuncType<?, ?>) {
			throw new UnsupportedOperationException();
		}

		if (term == null) {
			final Z3ConstDecl<DeclType> z3ConstDecl = (Z3ConstDecl<DeclType>) getDecl();
			final FuncDecl funcDecl = z3ConstDecl.getSymbol();
			term = context.mkConst(funcDecl);
		}

		return term;
	}
}
