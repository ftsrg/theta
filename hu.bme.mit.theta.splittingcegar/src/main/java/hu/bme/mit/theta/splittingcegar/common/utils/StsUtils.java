package hu.bme.mit.theta.splittingcegar.common.utils;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;

import hu.bme.mit.theta.core.LitExpr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.RatType;

public class StsUtils {

	/**
	 * Gets a concrete state from the valuation. Missing variables are added
	 * with some default value.
	 */
	public static Valuation getConcreteState(final Model model, final int i, final Collection<VarDecl<?>> variables) {
		final Valuation.Builder builder = Valuation.builder();

		for (final VarDecl<?> varDecl : variables) {
			final Optional<? extends LitExpr<?>> optValue = model.eval(varDecl.getConstDecl(i));

			if (optValue.isPresent()) {
				final LitExpr<?> value = optValue.get();
				builder.put(varDecl, value);

			} else {
				final Type type = varDecl.getType();
				final LitExpr<?> value = getAny(type);
				builder.put(varDecl, value);
			}
		}

		return builder.build();
	}

	private static LitExpr<?> getAny(final Type type) {
		if (type instanceof BoolType) {
			return False();
		} else if (type instanceof IntType) {
			return Int(0);
		} else if (type instanceof RatType) {
			return Rat(0, 1);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	/**
	 * Gets a concrete path from the valuation. Missing variables are added with
	 * some default value.
	 */
	public static List<Valuation> extractTrace(final Model model, final int length,
			final Collection<VarDecl<?>> variables) {
		final List<Valuation> trace = new ArrayList<>(length);
		for (int i = 0; i < length; ++i)
			trace.add(getConcreteState(model, i, variables));
		return trace;
	}
}
