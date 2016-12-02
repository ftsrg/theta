package hu.bme.mit.theta.formalism.tcfa.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.decl.impl.AbstractDecl;
import hu.bme.mit.theta.core.expr.RefExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.DeclVisitor;

public final class TcfaParamDecl<DeclType extends Type> extends AbstractDecl<DeclType> {

	public static enum Kind {
		VAL, VAR_REF, CLOCK_REF;
	}

	private static final int HASH_SEED = 4219;
	private static final String DECL_LABEL = "TcfaParam";

	private final Kind kind;

	protected TcfaParamDecl(final String name, final DeclType type, final Kind kind) {
		super(name, type);
		this.kind = checkNotNull(kind);
	}

	public static <DeclType extends Type> TcfaParamDecl<DeclType> of(final String name, final DeclType type,
			final Kind kind) {
		return new TcfaParamDecl<>(name, type, kind);
	}

	public Kind getKind() {
		return kind;
	}

	@Override
	public RefExpr<DeclType> getRef() {
		throw new UnsupportedOperationException();
	}

	@Override
	public <P, R> R accept(final DeclVisitor<? super P, ? extends R> visitor, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	protected String getDeclLabel() {
		return DECL_LABEL;
	}

}
