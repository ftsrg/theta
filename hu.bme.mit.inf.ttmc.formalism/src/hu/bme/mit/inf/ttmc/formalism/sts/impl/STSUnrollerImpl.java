package hu.bme.mit.inf.ttmc.formalism.sts.impl;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.model.Model;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.utils.PathUtils;

class STSUnrollerImpl {

	private final STS sts;

	public STSUnrollerImpl(final STS sts) {
		this.sts = sts;
	}

	public Expr<? extends BoolType> unroll(final Expr<? extends BoolType> expr, final int i) {
		return PathUtils.unfold(expr, i);
	}

	public Collection<? extends Expr<? extends BoolType>> unroll(
			final Collection<? extends Expr<? extends BoolType>> exprs, final int i) {
		return exprs.stream().map(e -> unroll(e, i)).collect(Collectors.toSet());
	}

	public Collection<? extends Expr<? extends BoolType>> init(final int i) {
		return unroll(sts.getInit(), i);
	}

	public Collection<? extends Expr<? extends BoolType>> trans(final int i) {
		return unroll(sts.getTrans(), i);
	}

	public Collection<? extends Expr<? extends BoolType>> inv(final int i) {
		return unroll(sts.getInvar(), i);
	}

	public Expr<? extends BoolType> prop(final int i) {
		return unroll(sts.getProp(), i);
	}

	public Valuation getConcreteState(final Model model, final int i,
			final Collection<VarDecl<? extends Type>> variables) {

		final Valuation.Builder builder = Valuation.builder();

		for (final VarDecl<? extends Type> varDecl : variables) {
			LitExpr<? extends Type> value = null;
			try {
				value = model.eval(varDecl.getConstDecl(i)).get();
			} catch (final Exception ex) {
				value = varDecl.getType().getAny();
			}
			builder.put(varDecl, value);
		}

		return builder.build();
	}

	public List<Valuation> extractTrace(final Model model, final int length,
			final Collection<VarDecl<? extends Type>> variables) {

		final List<Valuation> trace = new ArrayList<>(length);
		for (int i = 0; i < length; ++i)
			trace.add(getConcreteState(model, i, variables));
		return trace;
	}

	public Expr<? extends BoolType> foldin(final Expr<? extends BoolType> expr, final int i) {
		return PathUtils.fold(expr, i);
	}

}
