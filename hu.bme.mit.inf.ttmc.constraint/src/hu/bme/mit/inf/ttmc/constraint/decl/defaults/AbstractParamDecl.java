package hu.bme.mit.inf.ttmc.constraint.decl.defaults;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.ParamRefExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public abstract class AbstractParamDecl<DeclType extends Type> extends AbstractDecl<DeclType, ParamDecl<DeclType>>
		implements ParamDecl<DeclType> {

	private static final int HASH_SEED = 6949;
	private static final String DECL_LABEL = "Param";

	private final ConstraintManager manager;

	private volatile ParamRefExpr<DeclType> ref;

	public AbstractParamDecl(final ConstraintManager manager, final String name, final DeclType type) {
		super(name, type);
		this.manager = manager;
	}

	@Override
	public ParamRefExpr<DeclType> getRef() {
		if (ref == null) {
			ref = manager.getExprFactory().Ref(this);
		}

		return ref;
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
