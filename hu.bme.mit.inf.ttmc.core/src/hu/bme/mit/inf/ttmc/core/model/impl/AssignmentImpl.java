package hu.bme.mit.inf.ttmc.core.model.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.core.decl.Decl;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.model.Assignment;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;

public final class AssignmentImpl implements Assignment {

	private final Collection<Decl<?, ?>> decls;
	private final Map<Decl<?, ?>, LitExpr<?>> declToExpr;

	private static final Assignment EMPTY;

	static {
		EMPTY = new AssignmentImpl();
	}

	public static Assignment empty() {
		return EMPTY;
	}

	public AssignmentImpl() {
		this(new HashMap<>());
	}

	public AssignmentImpl(final Map<Decl<?, ?>, LitExpr<?>> constToExpr) {
		this.declToExpr = new HashMap<>(constToExpr);
		this.decls = ImmutableList.copyOf(constToExpr.keySet());
	}

	@Override
	public <DeclType extends Type, DeclKind extends Decl<DeclType, DeclKind>> Optional<LitExpr<DeclType>> eval(final Decl<DeclType, DeclKind> decl) {
		checkNotNull(decl);

		if (declToExpr.containsKey(decl)) {

			@SuppressWarnings("unchecked")
			final LitExpr<DeclType> val = (LitExpr<DeclType>) declToExpr.get(decl);
			return Optional.of(val);
		}

		return Optional.empty();
	}

	@Override
	public Collection<? extends Decl<?, ?>> getDecls() {
		return decls;
	}

	@Override
	public String toString() {
		final StringJoiner sj = new StringJoiner(", ", "Assignment(", ")");
		for (final Decl<?, ?> decl : decls) {
			final StringBuilder sb = new StringBuilder();
			sb.append(decl.getName());
			sb.append(" <- ");
			final Optional<?> val = eval(decl);
			assert val.isPresent();
			sb.append(val.get());
			sj.add(sb);
		}
		return sj.toString();
	}

	@Override
	public Expr<? extends BoolType> toExpr() {
		final List<Expr<? extends BoolType>> ops = new ArrayList<>(declToExpr.size());
		for (final Entry<Decl<?, ?>, LitExpr<?>> entry : declToExpr.entrySet()) {
			ops.add(Exprs.Eq(entry.getKey().getRef(), entry.getValue()));
		}
		if (ops.size() == 0) {
			return Exprs.True();
		} else if (ops.size() == 1) {
			return ops.get(0);
		} else {
			return Exprs.And(ops);
		}
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof AssignmentImpl) {
			final AssignmentImpl that = (AssignmentImpl) obj;
			return this.declToExpr.equals(that.declToExpr);
		} else {
			return false;
		}
	}

	private volatile int hashCode = 0;

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = 31 * result + declToExpr.hashCode();
			hashCode = result;
		}
		return result;
	}
}
