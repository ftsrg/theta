package hu.bme.mit.theta.formalism.tcfa.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Arrays;
import java.util.List;
import java.util.Optional;

import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.Assignment;
import hu.bme.mit.theta.formalism.tcfa.TCFA;

public final class TcfaSpec {

	private final TcfaSpecSymbol tcfaSpecSymbol;
	private final Assignment assignment;

	private TcfaSpec(final TcfaSpecSymbol tcfaSpecSymbol, final Assignment assignment) {
		this.tcfaSpecSymbol = checkNotNull(tcfaSpecSymbol);
		this.assignment = checkNotNull(assignment);
	}

	static TcfaSpec create(final TcfaSpecSymbol tcfaSpecSymbol, final Assignment assignment) {
		return new TcfaSpec(tcfaSpecSymbol, assignment);
	}

	////

	public TCFA createTcfa(final String name, final Expr<?>... params) {
		return createTcfa(name, Arrays.asList(params));
	}

	public TCFA createTcfa(final String name, final List<? extends Expr<?>> params) {
		final TcfaDeclSymbol tcfaDeclSymbol = resolveTcfaDeclSymbol(name);
		final TCFA tcfa = tcfaDeclSymbol.instantiate(assignment, params);
		return tcfa;
	}

	private TcfaDeclSymbol resolveTcfaDeclSymbol(final String name) {
		final Optional<Symbol> optSymbol = tcfaSpecSymbol.resolve(name);
		checkArgument(optSymbol.isPresent());
		final Symbol symbol = optSymbol.get();
		checkArgument(symbol instanceof TcfaDeclSymbol);
		final TcfaDeclSymbol tcfaDeclSymbol = (TcfaDeclSymbol) symbol;
		return tcfaDeclSymbol;
	}

}