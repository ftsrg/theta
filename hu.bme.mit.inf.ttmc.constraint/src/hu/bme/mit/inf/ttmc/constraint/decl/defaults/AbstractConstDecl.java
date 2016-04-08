package hu.bme.mit.inf.ttmc.constraint.decl.defaults;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.DeclVisitor;

public abstract class AbstractConstDecl<DeclType extends Type> extends AbstractDecl<DeclType, ConstDecl<DeclType>>
		implements ConstDecl<DeclType> {

	private static final int HASH_SEED = 5351;
	private static final String DECL_LABEL = "Const";

	private final ConstraintManager manager;

	private volatile ConstRefExpr<DeclType> ref;

	public AbstractConstDecl(final ConstraintManager manager, final String name, final DeclType type) {
		super(name, type);
		this.manager = manager;
	}

	@Override
	public ConstRefExpr<DeclType> getRef() {
		if (ref == null) {
			ref = manager.getExprFactory().Ref(this);
		}

		return ref;
	}

	@Override
	public final <P, R> R accept(final DeclVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	protected final int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	protected final String getDeclLabel() {
		return DECL_LABEL;
	}

}
