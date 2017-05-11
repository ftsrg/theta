package hu.bme.mit.theta.core.model.impl;

import static com.google.common.base.Preconditions.checkArgument;
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

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.Exprs;
import hu.bme.mit.theta.core.model.Assignment;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;

public final class AssignmentImpl implements Assignment {

	private final Collection<Decl<?>> decls;
	private final Map<Decl<?>, Expr<?>> declToExpr;

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

	public AssignmentImpl(final List<? extends Decl<?>> decls, final List<? extends Expr<?>> exprs) {
		this(zip(decls, exprs));
	}

	private static <K, V> Map<K, V> zip(final List<? extends K> keys, final List<? extends V> values) {
		checkArgument(keys.size() == values.size());
		final HashMap<K, V> result = new HashMap<>();
		for (int i = 0; i < keys.size(); i++) {
			final K key = keys.get(i);
			final V value = values.get(i);
			checkArgument(!result.keySet().contains(key));
			result.put(key, value);
		}
		return result;
	}

	public AssignmentImpl(final Map<? extends Decl<?>, ? extends Expr<?>> map) {
		checkAssignmentMap(map);
		this.declToExpr = new HashMap<>(map);
		this.decls = ImmutableList.copyOf(map.keySet());
	}

	private static void checkAssignmentMap(final Map<? extends Decl<?>, ? extends Expr<?>> declToExpr) {

		for (final Entry<? extends Decl<?>, ? extends Expr<?>> entry : declToExpr.entrySet()) {
			final Decl<?> decl = entry.getKey();
			final Expr<?> expr = entry.getValue();
			checkArgument(expr.getType().isLeq(decl.getType()));
		}
	}

	@Override
	public <DeclType extends Type> Optional<Expr<DeclType>> eval(final Decl<DeclType> decl) {
		checkNotNull(decl);

		if (declToExpr.containsKey(decl)) {

			@SuppressWarnings("unchecked")
			final Expr<DeclType> val = (Expr<DeclType>) declToExpr.get(decl);
			return Optional.of(val);
		}

		return Optional.empty();
	}

	@Override
	public Collection<? extends Decl<?>> getDecls() {
		return decls;
	}

	@Override
	public String toString() {
		final StringJoiner sj = new StringJoiner(", ", "Assignment(", ")");
		for (final Decl<?> decl : decls) {
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
		for (final Entry<Decl<?>, Expr<?>> entry : declToExpr.entrySet()) {
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
