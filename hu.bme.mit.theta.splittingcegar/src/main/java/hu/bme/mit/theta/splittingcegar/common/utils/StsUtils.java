package hu.bme.mit.theta.splittingcegar.common.utils;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.Type;

public class StsUtils {

	/**
	 * Gets a concrete state from the valuation. Missing variables are added
	 * with some default value.
	 */
	public static Valuation getConcreteState(final Model model, final int i, final Collection<VarDecl<?>> variables) {
		final Valuation.Builder builder = Valuation.builder();

		for (final VarDecl<?> varDecl : variables) {
			LitExpr<?> value = null;
			try {
				value = model.eval(varDecl.getConstDecl(i)).get();
			} catch (final Exception ex) {
				value = varDecl.getType().getAny();
			}
			builder.put(varDecl, value);
		}

		return builder.build();
	}

	/**
	 * Gets a concrete path from the valuation. Missing variables are added with
	 * some default value.
	 */
	public static List<Valuation> extractTrace(final Model model, final int length,
			final Collection<VarDecl<? extends Type>> variables) {
		final List<Valuation> trace = new ArrayList<>(length);
		for (int i = 0; i < length; ++i)
			trace.add(getConcreteState(model, i, variables));
		return trace;
	}
}
