package hu.bme.mit.theta.formalism.tcfa.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.expr.VarRefExpr;
import hu.bme.mit.theta.core.model.Assignment;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.ta.expr.ClockRefExpr;
import hu.bme.mit.theta.formalism.tcfa.dsl.TcfaParamDecl.Kind;

public class TcfaParamBinding implements Assignment {

	final List<TcfaParamDecl<?>> params;
	final Map<Decl<?>, Expr<?>> paramToArg;

	private TcfaParamBinding(final List<? extends TcfaParamDecl<?>> params, final List<? extends Expr<?>> args) {
		checkNotNull(params);
		checkNotNull(args);
		checkArgument(params.size() == args.size());

		this.params = ImmutableList.copyOf(params);
		this.paramToArg = new HashMap<>();

		for (int i = 0; i < params.size(); i++) {
			final TcfaParamDecl<?> param = params.get(i);
			final Expr<?> arg = args.get(i);
			checkParamBinding(param, arg);
			paramToArg.put(param, arg);
		}
	}

	public static TcfaParamBinding create(final List<? extends TcfaParamDecl<?>> params,
			final List<? extends Expr<?>> args) {
		return new TcfaParamBinding(params, args);
	}

	////

	private static void checkParamBinding(final TcfaParamDecl<?> param, final Expr<?> arg) {
		checkArgument(arg.getType().isLeq(param.getType()));
		if (param.getKind() == Kind.VAL) {
			checkArgument(arg instanceof LitExpr);
		} else if (param.getKind() == Kind.VAR_REF) {
			checkArgument((arg instanceof VarRefExpr) && !(arg instanceof ClockRefExpr));
		} else if (param.getKind() == Kind.CLOCK_REF) {
			checkArgument(arg instanceof ClockRefExpr);
		} else {
			throw new AssertionError();
		}
	}

	////

	@Override
	public List<TcfaParamDecl<?>> getDecls() {
		return params;
	}

	@Override
	public <DeclType extends Type> Optional<Expr<DeclType>> eval(final Decl<DeclType> decl) {
		@SuppressWarnings("unchecked")
		final Expr<DeclType> value = (Expr<DeclType>) paramToArg.get(decl);
		return Optional.ofNullable(value);
	}

	@Override
	public Expr<? extends BoolType> toExpr() {
		throw new UnsupportedOperationException();
	}

}
