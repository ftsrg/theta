package hu.bme.mit.inf.ttmc.formalism.utils;

import static com.google.common.base.Preconditions.checkState;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprRewriterVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.decl.IndexedConstDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.impl.Exprs2;

public class PathUtils {

	private static final UnfoldVisitor UNFOLD_VISITOR;
	private static final FoldVisitor FOLD_VISITOR;

	static {
		UNFOLD_VISITOR = new UnfoldVisitor();
		FOLD_VISITOR = new FoldVisitor();
	}

	private PathUtils() {
	}

	////

	public static <T extends Type> Expr<T> unfold(final Expr<T> expr, final int i) {
		@SuppressWarnings("unchecked")
		final Expr<T> result = (Expr<T>) expr.accept(UNFOLD_VISITOR, i);
		return result;
	}

	public static <T extends Type> Expr<T> fold(final Expr<T> expr, final int i) {
		@SuppressWarnings("unchecked")
		final Expr<T> result = (Expr<T>) expr.accept(FOLD_VISITOR, i);
		return result;
	}

	////

	private static final class UnfoldVisitor extends ExprRewriterVisitor<Integer>
			implements ProgExprVisitor<Integer, Expr<?>> {

		private UnfoldVisitor() {
		}

		////

		@Override
		public <ExprType extends Type> Expr<? extends ExprType> visit(final PrimedExpr<ExprType> expr,
				final Integer param) {
			final int i = param;
			final Expr<? extends ExprType> op = expr.getOp();
			@SuppressWarnings("unchecked")
			final Expr<? extends ExprType> res = (Expr<? extends ExprType>) op.accept(this, i + 1);
			return res;
		}

		@Override
		public <DeclType extends Type> Expr<? extends DeclType> visit(final VarRefExpr<DeclType> expr,
				final Integer param) {
			final int i = param;
			final VarDecl<DeclType> varDecl = expr.getDecl();
			final ConstDecl<DeclType> constDecl = varDecl.getConstDecl(i);
			final ConstRefExpr<DeclType> constRefExpr = constDecl.getRef();
			return constRefExpr;
		}

		@Override
		public <ReturnType extends Type> Expr<?> visit(final ProcRefExpr<ReturnType> expr, final Integer param) {
			// TODO Auto-generated method stub
			throw new UnsupportedOperationException("TODO: auto-generated method stub");
		}

		@Override
		public <ReturnType extends Type> Expr<?> visit(final ProcCallExpr<ReturnType> expr, final Integer param) {
			// TODO Auto-generated method stub
			throw new UnsupportedOperationException("TODO: auto-generated method stub");
		}
	}

	private static final class FoldVisitor extends ExprRewriterVisitor<Integer> {

		private FoldVisitor() {
		}

		////

		@Override
		public <DeclType extends Type> Expr<DeclType> visit(final ConstRefExpr<DeclType> expr, final Integer i) {
			final ConstDecl<DeclType> constDecl = expr.getDecl();

			if (constDecl instanceof IndexedConstDecl<?>) {
				final IndexedConstDecl<DeclType> indexedConstDecl = (IndexedConstDecl<DeclType>) constDecl;
				final int index = indexedConstDecl.getIndex();

				int nPrimes = index - i;
				checkState(nPrimes >= 0);

				final VarDecl<DeclType> varDecl = indexedConstDecl.getVarDecl();
				Expr<DeclType> res = varDecl.getRef();
				while (nPrimes > 0) {
					res = Exprs2.Prime(res);
					nPrimes--;
				}

				return res;
			} else {
				return expr;
			}
		}
	}

}
