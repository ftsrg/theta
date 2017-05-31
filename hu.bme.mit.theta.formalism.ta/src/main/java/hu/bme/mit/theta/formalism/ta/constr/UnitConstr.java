package hu.bme.mit.theta.formalism.ta.constr;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.rattype.RatType;

public abstract class UnitConstr extends AtomicConstr {

	private final VarDecl<RatType> var;

	private volatile int hashCode = 0;

	protected UnitConstr(final VarDecl<RatType> var, final int bound) {
		super(bound);
		this.var = checkNotNull(var);
	}

	public final VarDecl<RatType> getVar() {
		return var;
	}

	@Override
	public Collection<VarDecl<RatType>> getVars() {
		return ImmutableSet.of(var);
	}

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = getHashSeed();
			result = 31 * result + var.hashCode();
			result = 31 * result + getBound();
			hashCode = result;
		}
		return result;
	}

	@Override
	public final String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(var.getName());
		sb.append(" ");
		sb.append(getOperatorLabel());
		sb.append(" ");
		sb.append(getBound());
		return sb.toString();
	}

	protected abstract int getHashSeed();

	protected abstract String getOperatorLabel();

}
