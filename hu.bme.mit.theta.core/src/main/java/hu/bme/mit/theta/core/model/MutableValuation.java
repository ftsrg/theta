package hu.bme.mit.theta.core.model;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.Decl;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.LitExpr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class MutableValuation implements Valuation {
	private static final int HASH_SEED = 2141;
	private final Map<Decl<?>, Expr<?>> declToExpr;

	public MutableValuation() {
		this.declToExpr = new LinkedHashMap<>();
	}

	public static MutableValuation copyOf(final Valuation val) {
		final MutableValuation result = new MutableValuation();
		for (final Decl<?> decl : val.getDecls()) {
			result.put(decl, val.eval(decl).get());
		}
		return result;
	}

	public MutableValuation put(final Decl<?> decl, final LitExpr<?> value) {
		checkArgument(value.getType().equals(decl.getType()));
		declToExpr.put(decl, value);
		return this;
	}

	@Override
	public Collection<? extends Decl<?>> getDecls() {
		return Collections.unmodifiableSet(declToExpr.keySet());
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
	public <DeclType extends Type> Optional<LitExpr<DeclType>> eval(final Decl<DeclType> decl) {
		checkNotNull(decl);
		if (declToExpr.containsKey(decl)) {
			@SuppressWarnings("unchecked")
			final LitExpr<DeclType> val = (LitExpr<DeclType>) declToExpr.get(decl);
			return Optional.of(val);
		}
		return Optional.empty();
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder("Valuation")
				.addAll(declToExpr.entrySet(), e -> e.getKey().getName() + " <- " + e.getValue()).toString();
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof MutableValuation) {
			final MutableValuation that = (MutableValuation) obj;
			return this.declToExpr.equals(that.declToExpr);
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		return HASH_SEED * 31 + declToExpr.hashCode();
	}
}
