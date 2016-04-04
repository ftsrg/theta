package hu.bme.mit.inf.ttmc.constraint.z3.trasform;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.decl.Decl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public class Z3Transformator {

	final Z3TypeVisitor typeVisitor;
	final Z3DeclVisitor declVisitor;
	final Z3ExprVisitor exprVisitor;

	public Z3Transformator(final Context context) {
		this.typeVisitor = new Z3TypeVisitor(this, context);
		this.declVisitor = new Z3DeclVisitor(this, context);
		this.exprVisitor = new Z3ExprVisitor(this, context);
	}

	public com.microsoft.z3.Sort transform(final Type type) {
		return type.accept(typeVisitor, null);
	}

	public com.microsoft.z3.FuncDecl transform(final Decl<?, ?> decl) {
		return decl.accept(declVisitor, null);
	}

	public com.microsoft.z3.Expr transform(final Expr<?> expr) {
		return expr.accept(exprVisitor, null);
	}

}
