
package hu.bme.mit.inf.ttmc.core.solver;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Map;
import java.util.Optional;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;

public interface Model {
	
	public <T extends Type> Optional<Expr<T>> eval(final ConstDecl<T> decl);
	public <T extends Type> Optional<Expr<T>> eval(final Expr<T> expr);
	
	public Model with(final Map<? extends ConstDecl<?>, ? extends Expr<?>> mapping);
	public default <T extends Type> Model with(final ConstDecl<? extends T> constDecl, final Expr<? extends T> expr) {
		checkNotNull(constDecl);
		checkNotNull(expr);
		return with(ImmutableMap.of(constDecl, expr));
	}
	
	public Model without(final Collection<? extends ConstDecl<?>> constDecls);
	public default Model without(final ConstDecl<?> constDecl) {
		checkNotNull(constDecl);
		return without(ImmutableSet.of(constDecl));
	}
	
	public Expr<? extends BoolType> toExpr();
	
}
