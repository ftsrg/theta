package hu.bme.mit.inf.ttmc.constraint.z3.trasform;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.decl.Decl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public class Z3TransformationManager {

	final Z3TypeTransformator typeTransformator;
	final Z3DeclTransformator declTransformator;
	final Z3ExprTransformator exprTransformator;

	public Z3TransformationManager(final Context context) {
		this.typeTransformator = new Z3TypeTransformator(this, context);
		this.declTransformator = new Z3DeclTransformator(this, context);
		this.exprTransformator = new Z3ExprTransformator(this, context);
	}

	public com.microsoft.z3.Sort transform(final Type type) {
		return typeTransformator.transform(type);
	}

	public com.microsoft.z3.FuncDecl transform(final Decl<?, ?> decl) {
		return declTransformator.transform(decl);
	}

	public com.microsoft.z3.Expr transform(final Expr<?> expr) {
		return exprTransformator.transform(expr);
	}

}
