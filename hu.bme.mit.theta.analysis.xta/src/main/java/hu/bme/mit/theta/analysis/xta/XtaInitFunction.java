package hu.bme.mit.theta.analysis.xta;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.ImmutableList.toImmutableList;
import static hu.bme.mit.theta.core.expr.Exprs.False;
import static hu.bme.mit.theta.core.expr.Exprs.Int;

import java.util.Collection;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.xta.XtaProcess;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;
import hu.bme.mit.theta.formalism.xta.XtaSystem;

final class XtaInitFunction<S extends State, P extends Prec> implements InitFunction<XtaState<S>, P> {
	private final XtaSystem system;
	private final InitFunction<S, ? super P> initFunction;

	private XtaInitFunction(final XtaSystem system, final InitFunction<S, ? super P> initFunction) {
		this.system = checkNotNull(system);
		this.initFunction = checkNotNull(initFunction);
	}

	public static <S extends State, P extends Prec> XtaInitFunction<S, P> create(final XtaSystem system,
			final InitFunction<S, ? super P> initFunction) {
		return new XtaInitFunction<>(system, initFunction);
	}

	@Override
	public Collection<XtaState<S>> getInitStates(final P prec) {
		checkNotNull(prec);
		final List<Loc> initLocs = creatInitLocs(system);
		final Valuation initVal = createInitVal(system);
		final Collection<? extends S> initStates = initFunction.getInitStates(prec);
		return XtaState.collectionOf(initLocs, initVal, initStates);
	}

	private static ImmutableList<Loc> creatInitLocs(final XtaSystem system) {
		return system.getProcesses().stream().map(XtaProcess::getInitLoc).collect(toImmutableList());
	}

	private static Valuation createInitVal(final XtaSystem system) {
		final Valuation.Builder builder = Valuation.builder();
		for (final VarDecl<?> var : system.getVars()) {
			final Type type = var.getType();
			if (type instanceof BoolType) {
				builder.put(var, False());
			} else if (type instanceof IntType) {
				builder.put(var, Int(0));
			} else if (type instanceof RatType) {
				// var is a clock variable, do nothing
			} else {
				throw new UnsupportedOperationException();
			}
		}
		return builder.build();
	}

}
