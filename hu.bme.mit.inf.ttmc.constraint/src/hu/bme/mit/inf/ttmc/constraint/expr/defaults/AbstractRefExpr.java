package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.decl.Decl;
import hu.bme.mit.inf.ttmc.constraint.expr.RefExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public abstract class AbstractRefExpr<DeclType extends Type, DeclKind extends Decl<DeclType>>
		extends AbstractExpr<DeclType> implements RefExpr<DeclType, DeclKind> {

	private final DeclKind decl;

	private volatile int hashCode = 0;

	public AbstractRefExpr(final DeclKind decl) {
		this.decl = checkNotNull(decl);
	}

	@Override
	public DeclKind getDecl() {
		return decl;
	}

	@Override
	public int hashCode() {
		if (hashCode == 0) {
			hashCode = getHashSeed();
			hashCode = 31 * hashCode + decl.hashCode();
		}

		return hashCode;
	}

	@Override
	public final String toString() {
		return getDecl().getName();
	}

}
