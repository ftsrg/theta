package hu.bme.mit.theta.formalism.xta.analysis;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.ImmutableList.toImmutableList;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import java.util.Collection;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.BasicValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.formalism.xta.XtaProcess;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;
import hu.bme.mit.theta.formalism.xta.XtaSystem;

final class XtaInitFunc<S extends State, P extends Prec> implements InitFunc<XtaState<S>, P> {
	private final XtaSystem system;
	private final InitFunc<S, ? super P> initFunc;

	private XtaInitFunc(final XtaSystem system, final InitFunc<S, ? super P> initFunc) {
		this.system = checkNotNull(system);
		this.initFunc = checkNotNull(initFunc);
	}

	public static <S extends State, P extends Prec> XtaInitFunc<S, P> create(final XtaSystem system,
			final InitFunc<S, ? super P> initFunc) {
		return new XtaInitFunc<>(system, initFunc);
	}

	@Override
	public Collection<XtaState<S>> getInitStates(final P prec) {
		checkNotNull(prec);
		final List<Loc> initLocs = creatInitLocs(system);
		final Valuation initVal = createInitVal(system);
		final Collection<? extends S> initStates = initFunc.getInitStates(prec);
		return XtaState.collectionOf(initLocs, initVal, initStates);
	}

	private static ImmutableList<Loc> creatInitLocs(final XtaSystem system) {
		return system.getProcesses().stream().map(XtaProcess::getInitLoc).collect(toImmutableList());
	}

	private static Valuation createInitVal(final XtaSystem system) {
		final BasicValuation.Builder builder = BasicValuation.builder();
		for (final VarDecl<?> var : system.getDataVars()) {
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
