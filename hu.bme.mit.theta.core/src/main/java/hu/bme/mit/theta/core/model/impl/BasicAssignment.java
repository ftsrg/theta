package hu.bme.mit.theta.core.model.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.Decl;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.model.Assignment;
import hu.bme.mit.theta.core.type.booltype.BoolType;

/**
 * Basic implementation of an assignment.
 */
public final class BasicAssignment implements Assignment {

	private final Collection<Decl<?>> decls;
	private final Map<Decl<?>, Expr<?>> declToExpr;

	private static final Assignment EMPTY;

	static {
		EMPTY = new BasicAssignment();
	}

	public static Assignment empty() {
		return EMPTY;
	}

	public BasicAssignment() {
		this(new HashMap<>());
	}

	public BasicAssignment(final Map<? extends Decl<?>, ? extends Expr<?>> map) {
		checkAssignmentMap(map);
		this.declToExpr = new HashMap<>(map);
		this.decls = ImmutableList.copyOf(map.keySet());
	}

	private static void checkAssignmentMap(final Map<? extends Decl<?>, ? extends Expr<?>> declToExpr) {

		for (final Entry<? extends Decl<?>, ? extends Expr<?>> entry : declToExpr.entrySet()) {
			final Decl<?> decl = entry.getKey();
			final Expr<?> expr = entry.getValue();
			checkArgument(expr.getType().equals(decl.getType()));
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
		return ObjectUtils.toStringBuilder("Assignment")
				.addAll(declToExpr.entrySet(), e -> e.getKey().getName() + " <- " + e.getValue()).toString();
	}

	@Override
	public Expr<BoolType> toExpr() {
		final List<Expr<BoolType>> ops = new ArrayList<>(declToExpr.size());
		for (final Entry<Decl<?>, Expr<?>> entry : declToExpr.entrySet()) {
			ops.add(Eq(entry.getKey().getRef(), entry.getValue()));
		}
		if (ops.size() == 0) {
			return True();
		} else if (ops.size() == 1) {
			return ops.get(0);
		} else {
			return And(ops);
		}
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof BasicAssignment) {
			final BasicAssignment that = (BasicAssignment) obj;
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
