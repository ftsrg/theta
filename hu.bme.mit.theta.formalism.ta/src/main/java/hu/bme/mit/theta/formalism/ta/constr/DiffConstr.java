package hu.bme.mit.theta.formalism.ta.constr;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.rattype.RatType;

public abstract class DiffConstr extends AtomicConstr {

	private final VarDecl<RatType> leftVar;
	private final VarDecl<RatType> rightVar;

	private volatile int hashCode = 0;

	protected DiffConstr(final VarDecl<RatType> leftVar, final VarDecl<RatType> rightVar, final int bound) {
		super(bound);
		this.leftVar = checkNotNull(leftVar);
		this.rightVar = checkNotNull(rightVar);
	}

	public final VarDecl<RatType> getLeftVar() {
		return leftVar;
	}

	public final VarDecl<RatType> getRightVar() {
		return rightVar;
	}

	@Override
	public Collection<VarDecl<RatType>> getVars() {
		return ImmutableSet.of(leftVar, rightVar);
	}

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = getHashSeed();
			result = 31 * result + leftVar.hashCode();
			result = 31 * result + rightVar.hashCode();
			result = 31 * result + getBound();
			hashCode = result;
		}
		return result;
	}

	@Override
	public final String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(leftVar.getName());
		sb.append(" - ");
		sb.append(rightVar.getName());
		sb.append(' ');
		sb.append(getOperatorLabel());
		sb.append(' ');
		sb.append(getBound());
		return sb.toString();
	}

	protected abstract int getHashSeed();

	protected abstract String getOperatorLabel();

}
