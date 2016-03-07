package hu.bme.mit.inf.ttmc.formalism;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.StringJoiner;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.decl.VarDecl;

public class State {
	
	private final Map<VarDecl<?>, Expr<?>> varToExpr;
	
	public State(final Map<VarDecl<?>, Expr<?>> varToExpr) {
		checkNotNull(varToExpr);
		this.varToExpr = new HashMap<>(varToExpr);
	}
	
	public <T extends Type> Optional<Expr<T>> eval(VarDecl<T> decl) {
		@SuppressWarnings("unchecked")
		final Expr<T> value = (Expr<T>) varToExpr.get(decl);
		return Optional.ofNullable(value);
	}
	
	@Override
	public String toString() {
		final StringJoiner sj = new StringJoiner(", ", "State(", ")");
		for (Entry<VarDecl<?>, Expr<?>> entry : varToExpr.entrySet()) {
			final StringBuilder sb = new StringBuilder();
			sb.append(entry.getKey().getName());
			sb.append(" -> ");
			sb.append(entry.getValue().toString());
			
			sj.add(sb.toString());
		}
		
		return sj.toString();
	}
}
