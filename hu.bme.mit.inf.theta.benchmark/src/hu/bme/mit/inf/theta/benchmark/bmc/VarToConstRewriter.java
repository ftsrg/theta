package hu.bme.mit.inf.theta.benchmark.bmc;

import java.util.List;
import java.util.stream.Collectors;

import hu.bme.mit.inf.theta.core.decl.ConstDecl;
import hu.bme.mit.inf.theta.core.expr.ConstRefExpr;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.core.utils.impl.ExprRewriterVisitor;
import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.theta.formalism.common.expr.ProcCallExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.impl.Exprs2;
import hu.bme.mit.inf.theta.formalism.common.expr.visitor.ProcCallExprVisitor;
import hu.bme.mit.inf.theta.formalism.common.expr.visitor.VarRefExprVisitor;

public class VarToConstRewriter {

	private final VarToConstVisitor visitor;

	public VarToConstRewriter(final VarMap varMap) {
		visitor = new VarToConstVisitor(varMap);
	}

	public <T extends Type> Expr<T> rewrite(final Expr<T> expr, final IndexMap indexMap) {
		@SuppressWarnings("unchecked")
		final Expr<T> result = (Expr<T>) expr.accept(visitor, indexMap);
		return result;
	}

	private static class VarToConstVisitor extends ExprRewriterVisitor<IndexMap>
			implements VarRefExprVisitor<IndexMap, Expr<?>>, ProcCallExprVisitor<IndexMap, Expr<?>> {

		private final VarMap varMap;

		VarToConstVisitor(final VarMap varMap) {
			this.varMap = varMap;
		}

		////////

		@Override
		public <DeclType extends Type> ConstRefExpr<DeclType> visit(final VarRefExpr<DeclType> expr,
				final IndexMap indexMap) {
			final VarDecl<DeclType> varDecl = expr.getDecl();
			final int index = indexMap.getIndex(varDecl);

			final ConstDecl<DeclType> constDecl = varMap.getConstDecl(varDecl, index);
			final ConstRefExpr<DeclType> constRef = constDecl.getRef();

			return constRef;
		}

		@Override
		public <ReturnType extends Type> Expr<?> visit(ProcCallExpr<ReturnType> expr, IndexMap param) {
			List<Expr<?>> args = expr.getParams().stream()
				.map(arg -> arg.accept(this, param))
				.collect(Collectors.toList());

			return Exprs2.Call(expr.getProc(), args);
		}
	}

}