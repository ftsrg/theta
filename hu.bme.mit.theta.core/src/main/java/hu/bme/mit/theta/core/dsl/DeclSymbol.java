package hu.bme.mit.theta.core.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.Decl;

public class DeclSymbol implements Symbol {

	private static final int HASH_SEED = 8513;

	private volatile int hashCode = 0;

	private final Decl<?> decl;

	private DeclSymbol(final Decl<?> decl) {
		this.decl = checkNotNull(decl);
	}

	public static DeclSymbol of(final Decl<?> decl) {
		return new DeclSymbol(decl);
	}

	public Decl<?> getDecl() {
		return decl;
	}

	@Override
	public String getName() {
		return decl.getName();
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + decl.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof DeclSymbol) {
			final DeclSymbol that = (DeclSymbol) obj;
			return this.decl.equals(that.decl);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).add(decl).toString();
	}

}
