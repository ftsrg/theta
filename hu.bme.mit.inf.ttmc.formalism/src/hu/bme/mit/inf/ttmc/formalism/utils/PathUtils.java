package hu.bme.mit.inf.ttmc.formalism.utils;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.model.Model;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprRewriterVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;
import hu.bme.mit.inf.ttmc.formalism.common.decl.IndexedConstDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.impl.Exprs2;

public class PathUtils {

	private PathUtils() {
	}

	////

	public static <T extends Type> Expr<T> unfold(final Expr<T> expr, final VarIndexes indexes) {
		checkNotNull(expr);
		checkNotNull(indexes);

		final UnfoldVisitor visitor = new UnfoldVisitor(indexes);

		@SuppressWarnings("unchecked")
		final Expr<T> result = (Expr<T>) expr.accept(visitor, 0);

		return result;
	}

	public static <T extends Type> Expr<T> unfold(final Expr<T> expr, final int i) {
		checkArgument(i >= 0);
		return unfold(expr, VarIndexes.all(i));
	}

	public static <T extends Type> Expr<T> fold(final Expr<T> expr, final VarIndexes indexes) {
		checkNotNull(expr);
		checkNotNull(indexes);

		final FoldVisitor visitor = new FoldVisitor(indexes);

		@SuppressWarnings("unchecked")
		final Expr<T> result = (Expr<T>) expr.accept(visitor, null);

		return result;
	}

	public static <T extends Type> Expr<T> fold(final Expr<T> expr, final int i) {
		checkArgument(i >= 0);
		return fold(expr, VarIndexes.all(i));
	}

	public static Valuation extractValuation(final Model model, final VarIndexes indexes) {
		final Valuation.Builder builder = Valuation.builder();
		for (final ConstDecl<?> constDecl : model.getDecls()) {
			if (constDecl instanceof IndexedConstDecl) {
				final IndexedConstDecl<?> indexedConstDecl = (IndexedConstDecl<?>) constDecl;
				final VarDecl<?> varDecl = indexedConstDecl.getVarDecl();
				if (indexedConstDecl.getIndex() == indexes.get(varDecl)) {
					final LitExpr<?> value = model.eval(indexedConstDecl).get();
					builder.put(varDecl, value);
				}
			}
		}
		return builder.build();
	}

	public static Valuation extractValuation(final Model model, final int i) {
		checkArgument(i >= 0);
		return extractValuation(model, VarIndexes.all(i));
	}

	////

	private static final class UnfoldVisitor extends ExprRewriterVisitor<Integer>
			implements ProgExprVisitor<Integer, Expr<?>> {

		private final VarIndexes indexes;

		private UnfoldVisitor(final VarIndexes indexes) {
			this.indexes = indexes;
		}

		////

		@Override
		public <ExprType extends Type> Expr<? extends ExprType> visit(final PrimedExpr<ExprType> expr,
				final Integer offset) {
			final Expr<? extends ExprType> op = expr.getOp();
			@SuppressWarnings("unchecked")
			final Expr<? extends ExprType> res = (Expr<? extends ExprType>) op.accept(this, offset + 1);
			return res;
		}

		@Override
		public <DeclType extends Type> Expr<? extends DeclType> visit(final VarRefExpr<DeclType> expr,
				final Integer offset) {
			final VarDecl<DeclType> varDecl = expr.getDecl();
			final int index = indexes.get(varDecl) + offset;
			final ConstDecl<DeclType> constDecl = varDecl.getConstDecl(index);
			final ConstRefExpr<DeclType> constRefExpr = constDecl.getRef();
			return constRefExpr;
		}

		@Override
		public <ReturnType extends Type> Expr<?> visit(final ProcRefExpr<ReturnType> expr, final Integer offset) {
			// TODO Auto-generated method stub
			throw new UnsupportedOperationException("TODO: auto-generated method stub");
		}

		@Override
		public <ReturnType extends Type> Expr<?> visit(final ProcCallExpr<ReturnType> expr, final Integer offset) {
			// TODO Auto-generated method stub
			throw new UnsupportedOperationException("TODO: auto-generated method stub");
		}
	}

	private static final class FoldVisitor extends ExprRewriterVisitor<Void> {

		private final VarIndexes indexes;

		private FoldVisitor(final VarIndexes indexes) {
			this.indexes = indexes;
		}

		////

		@Override
		public <DeclType extends Type> Expr<DeclType> visit(final ConstRefExpr<DeclType> expr, final Void param) {
			final ConstDecl<DeclType> constDecl = expr.getDecl();

			if (constDecl instanceof IndexedConstDecl<?>) {
				final IndexedConstDecl<DeclType> indexedConstDecl = (IndexedConstDecl<DeclType>) constDecl;
				final VarDecl<DeclType> varDecl = indexedConstDecl.getVarDecl();

				final int index = indexedConstDecl.getIndex();

				int nPrimes = index - indexes.get(varDecl);
				checkArgument(nPrimes >= 0);

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

	////

}
