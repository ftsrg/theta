package hu.bme.mit.inf.ttmc.constraint.z3.trasform;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.decl.Decl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public class Z3TransformationManager {

	final Z3TypeTransformer typeTransformer;
	final Z3DeclTransformer declTransformer;
	final Z3ExprTransformer exprTransformer;

	public Z3TransformationManager(final Context context) {
		this.typeTransformer = new Z3TypeTransformer(this, context);
		this.declTransformer = new Z3DeclTransformer(this, context);
		this.exprTransformer = new Z3ExprTransformer(this, context);
	}

	public com.microsoft.z3.Sort transform(final Type type) {
		return typeTransformer.transform(type);
	}

	public com.microsoft.z3.FuncDecl transform(final Decl<?, ?> decl) {
		return declTransformer.transform(decl);
	}

	public com.microsoft.z3.Expr transform(final Expr<?> expr) {
		return exprTransformer.transform(expr);
	}

}
