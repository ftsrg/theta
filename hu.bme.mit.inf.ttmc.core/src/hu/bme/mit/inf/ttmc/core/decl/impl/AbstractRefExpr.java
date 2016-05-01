package hu.bme.mit.inf.ttmc.core.decl.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.core.decl.Decl;
import hu.bme.mit.inf.ttmc.core.expr.RefExpr;
import hu.bme.mit.inf.ttmc.core.expr.impl.AbstractExpr;
import hu.bme.mit.inf.ttmc.core.type.Type;

public abstract class AbstractRefExpr<DeclType extends Type, DeclKind extends Decl<DeclType, DeclKind>>
		extends AbstractExpr<DeclType> implements RefExpr<DeclType, DeclKind> {

	private final DeclKind decl;

	private volatile int hashCode = 0;

	public AbstractRefExpr(final DeclKind decl) {
		this.decl = checkNotNull(decl);
	}

	@Override
	public final DeclKind getDecl() {
		return decl;
	}

	@Override
	public final DeclType getType() {
		return decl.getType();
	}

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = getHashSeed();
			result = 31 * result + decl.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public final String toString() {
		return getDecl().getName();
	}

	protected abstract int getHashSeed();

}
