package hu.bme.mit.theta.analysis.zone.lu;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Exists;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Gt;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Lt;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.StringJoiner;

import com.google.common.collect.Lists;

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.zone.BoundFunc;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.core.utils.ExprUtils;

public final class LuZoneState implements ExprState {
	private static final int HASH_SEED = 5261;

	private final ZoneState zone;
	private final BoundFunc boundFunction;

	private volatile int hashCode = 0;
	private volatile Expr<BoolType> expr = null;

	private LuZoneState(final ZoneState zone, final BoundFunc boundFunction) {
		this.zone = checkNotNull(zone);
		this.boundFunction = checkNotNull(boundFunction);
	}

	public static LuZoneState of(final ZoneState zone, final BoundFunc boundFunction) {
		return new LuZoneState(zone, boundFunction);
	}

	public ZoneState getZone() {
		return zone;
	}

	public BoundFunc getBoundFunction() {
		return boundFunction;
	}

	public LuZoneState withBoundFunction(final BoundFunc boundFunction) {
		return LuZoneState.of(zone, boundFunction);
	}

	public boolean isBottom() {
		return zone.isBottom();
	}

	public boolean isLeq(final LuZoneState that) {
		return that.getBoundFunction().isLeq(this.getBoundFunction())
				&& this.getZone().isLeq(that.getZone(), that.boundFunction);
	}

	@Override
	public Expr<BoolType> toExpr() {
		Expr<BoolType> result = expr;
		if (result == null) {
			// TODO create class for mapping
			final Map<VarDecl<?>, ParamDecl<?>> mapping = new HashMap<>();
			final Expr<BoolType> zoneExpr = ExprUtils.close(zone.toExpr(), mapping);
			final Collection<Expr<BoolType>> conjuncts = new ArrayList<>();

			conjuncts.addAll(ExprUtils.getConjuncts(zoneExpr));
			final Collection<VarDecl<?>> vars = mapping.keySet();

			for (final VarDecl<?> vx : vars) {
				@SuppressWarnings("unchecked")
				final VarDecl<RatType> dx = (VarDecl<RatType>) vx;

				@SuppressWarnings("unchecked")
				final ParamDecl<RatType> dxp = (ParamDecl<RatType>) mapping.get(dx);

				final Expr<RatType> x = dx.getRef();
				final Expr<RatType> xp = dxp.getRef();

				final Optional<Integer> optLower = boundFunction.getLower(dx);
				if (optLower.isPresent()) {
					final int lower = optLower.get();
					final Expr<RatType> lx = Rat(lower, 1);
					// x > xp imply xp > L(x)
					final Expr<BoolType> lowerExpr = Imply(Gt(x, xp), Gt(xp, lx));
					conjuncts.add(lowerExpr);
				}

				final Optional<Integer> optUpper = boundFunction.getUpper(dx);
				if (optUpper.isPresent()) {
					final int upper = optUpper.get();
					final Expr<RatType> ux = Rat(upper, 1);
					// x < xp imply x > U(x)
					final Expr<BoolType> upperExpr = Imply(Lt(x, xp), Gt(x, ux));
					conjuncts.add(upperExpr);
				}
			}

			if (conjuncts.isEmpty()) {
				result = True();
			} else {
				result = Exists(Lists.newArrayList(mapping.values()), And(conjuncts));
			}

			expr = result;
		}
		return result;
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + zone.hashCode();
			result = 31 * result + boundFunction.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof LuZoneState) {
			final LuZoneState that = (LuZoneState) obj;
			return this.zone.equals(that.zone) && this.boundFunction.equals(that.boundFunction);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringJoiner sj = new StringJoiner("\n");
		sj.add(zone.toString());
		if (!boundFunction.getLowerVars().isEmpty()) {
			sj.add("L:");
			boundFunction.getLowerVars().forEach(c -> sj.add(c.getName() + " <- " + boundFunction.getLower(c).get()));
		}
		if (!boundFunction.getUpperVars().isEmpty()) {
			sj.add("U:");
			boundFunction.getUpperVars().forEach(c -> sj.add(c.getName() + " <- " + boundFunction.getUpper(c).get()));
		}
		return sj.toString();
	}

}
