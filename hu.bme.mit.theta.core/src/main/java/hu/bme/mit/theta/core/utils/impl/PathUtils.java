package hu.bme.mit.theta.core.utils.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.expr.Exprs.Prime;

import java.util.Collection;
import java.util.Optional;
import java.util.stream.Collectors;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.ConstRefExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.expr.PrimedExpr;
import hu.bme.mit.theta.core.expr.ProcCallExpr;
import hu.bme.mit.theta.core.expr.ProcRefExpr;
import hu.bme.mit.theta.core.expr.VarRefExpr;
import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.Type;

public class PathUtils {

	private PathUtils() {
	}

	////

	public static VarIndexing countPrimes(final Expr<?> expr) {
		return PrimeCounter.countPrimes(expr);
	}

	////

	public static <T extends Type> Expr<T> unfold(final Expr<T> expr, final VarIndexing indexing) {
		checkNotNull(expr);
		checkNotNull(indexing);

		final UnfoldVisitor visitor = new UnfoldVisitor(indexing);

		@SuppressWarnings("unchecked")
		final Expr<T> result = (Expr<T>) expr.accept(visitor, 0);

		return result;
	}

	public static <T extends Type> Expr<T> unfold(final Expr<T> expr, final int i) {
		checkArgument(i >= 0);
		return unfold(expr, VarIndexing.all(i));
	}

	public static <T extends Type> Collection<Expr<? extends T>> unfold(final Collection<Expr<? extends T>> exprs,
			final int i) {
		return exprs.stream().map(e -> PathUtils.unfold(e, i)).collect(Collectors.toSet());
	}

	public static <T extends Type> Expr<T> foldin(final Expr<T> expr, final VarIndexing indexing) {
		checkNotNull(expr);
		checkNotNull(indexing);

		final FoldinVisitor visitor = new FoldinVisitor(indexing);

		@SuppressWarnings("unchecked")
		final Expr<T> result = (Expr<T>) expr.accept(visitor, null);

		return result;
	}

	public static <T extends Type> Expr<T> foldin(final Expr<T> expr, final int i) {
		checkArgument(i >= 0);
		return foldin(expr, VarIndexing.all(i));
	}

	public static Valuation extractValuation(final Model model, final VarIndexing indexing) {
		final Valuation.Builder builder = Valuation.builder();
		for (final ConstDecl<?> constDecl : model.getDecls()) {
			if (constDecl instanceof IndexedConstDecl) {
				final IndexedConstDecl<?> indexedConstDecl = (IndexedConstDecl<?>) constDecl;
				final VarDecl<?> varDecl = indexedConstDecl.getVarDecl();
				if (indexedConstDecl.getIndex() == indexing.get(varDecl)) {
					final LitExpr<?> value = model.eval(indexedConstDecl).get();
					builder.put(varDecl, value);
				}
			}
		}
		return builder.build();
	}

	public static Valuation extractValuation(final Model model, final int i) {
		checkArgument(i >= 0);
		return extractValuation(model, VarIndexing.all(i));
	}

	public static Valuation extractValuation(final Model model, final VarIndexing indexing,
			final Collection<? extends VarDecl<? extends Type>> varDecls) {
		final Valuation.Builder builder = Valuation.builder();
		for (final VarDecl<? extends Type> varDecl : varDecls) {
			final int index = indexing.get(varDecl);
			final IndexedConstDecl<?> constDecl = varDecl.getConstDecl(index);
			final Optional<? extends LitExpr<?>> eval = model.eval(constDecl);
			if (eval.isPresent()) {
				builder.put(varDecl, eval.get());
			}
		}
		return builder.build();
	}

	public static Valuation extractValuation(final Model model, final int i,
			final Collection<? extends VarDecl<? extends Type>> varDecls) {
		checkArgument(i >= 0);
		return extractValuation(model, VarIndexing.all(i), varDecls);
	}

	////

	private static final class UnfoldVisitor extends ExprRewriterVisitor<Integer> {

		private final VarIndexing indexing;

		private UnfoldVisitor(final VarIndexing indexing) {
			this.indexing = indexing;
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
			final int index = indexing.get(varDecl) + offset;
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

	private static final class FoldinVisitor extends ExprRewriterVisitor<Void> {

		private final VarIndexing indexing;

		private FoldinVisitor(final VarIndexing indexing) {
			this.indexing = indexing;
		}

		////

		@Override
		public <DeclType extends Type> Expr<DeclType> visit(final ConstRefExpr<DeclType> expr, final Void param) {
			final ConstDecl<DeclType> constDecl = expr.getDecl();

			if (constDecl instanceof IndexedConstDecl<?>) {
				final IndexedConstDecl<DeclType> indexedConstDecl = (IndexedConstDecl<DeclType>) constDecl;
				final VarDecl<DeclType> varDecl = indexedConstDecl.getVarDecl();

				final int index = indexedConstDecl.getIndex();

				int nPrimes = index - indexing.get(varDecl);
				checkArgument(nPrimes >= 0);

				Expr<DeclType> res = varDecl.getRef();
				while (nPrimes > 0) {
					res = Prime(res);
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
