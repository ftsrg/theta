package hu.bme.mit.theta.core.utils;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;

import java.util.Collection;
import java.util.Optional;
import java.util.stream.Collectors;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.PrimeExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;

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
		final UnfoldHelper helper = new UnfoldHelper(indexing);
		final Expr<T> result = helper.unfold(expr, 0);
		return result;
	}

	public static <T extends Type> Expr<T> unfold(final Expr<T> expr, final int i) {
		checkArgument(i >= 0);
		return unfold(expr, VarIndexing.all(i));
	}

	public static <T extends Type> Collection<Expr<T>> unfold(final Collection<Expr<T>> exprs, final int i) {
		return exprs.stream().map(e -> PathUtils.unfold(e, i)).collect(Collectors.toSet());
	}

	public static <T extends Type> Expr<T> foldin(final Expr<T> expr, final VarIndexing indexing) {
		checkNotNull(expr);
		checkNotNull(indexing);
		final FoldinHelper helper = new FoldinHelper(indexing);
		final Expr<T> result = helper.foldin(expr);
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

	private static final class UnfoldHelper {

		private final VarIndexing indexing;

		private UnfoldHelper(final VarIndexing indexing) {
			this.indexing = indexing;
		}

		public <T extends Type> Expr<T> unfold(final Expr<T> expr, final int offset) {
			if (expr instanceof RefExpr) {
				final RefExpr<T> ref = (RefExpr<T>) expr;
				final Decl<T> decl = ref.getDecl();
				if (decl instanceof VarDecl) {
					final VarDecl<T> varDecl = (VarDecl<T>) decl;
					final int index = indexing.get(varDecl) + offset;
					final ConstDecl<T> constDecl = varDecl.getConstDecl(index);
					final RefExpr<T> refExpr = constDecl.getRef();
					return refExpr;
				}
			}

			if (expr instanceof PrimeExpr) {
				final PrimeExpr<T> prime = (PrimeExpr<T>) expr;
				final Expr<T> op = prime.getOp();
				return unfold(op, offset + 1);
			}

			return expr.rewrite(op -> unfold(op, offset));
		}
	}

	////

	private static final class FoldinHelper {

		private final VarIndexing indexing;

		private FoldinHelper(final VarIndexing indexing) {
			this.indexing = indexing;
		}

		public <T extends Type> Expr<T> foldin(final Expr<T> expr) {
			if (expr instanceof RefExpr) {
				final RefExpr<T> ref = (RefExpr<T>) expr;
				final Decl<T> decl = ref.getDecl();
				if (decl instanceof IndexedConstDecl) {
					final IndexedConstDecl<T> constDecl = (IndexedConstDecl<T>) decl;
					final VarDecl<T> varDecl = constDecl.getVarDecl();
					final int index = constDecl.getIndex();
					final int nPrimes = index - indexing.get(varDecl);
					checkArgument(nPrimes >= 0);
					final Expr<T> varRef = varDecl.getRef();
					return Prime(varRef, nPrimes);
				}
			}

			return expr.rewrite(this::foldin);
		}
	}

}
