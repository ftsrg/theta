package hu.bme.mit.inf.ttmc.analysis.algorithm;

import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.common.Product2;

public final class NullLabeling implements ARGLabeling<State, Void, Void, Object, Object, Object> {

	private static final NullLabeling INSTANCE;

	static {
		INSTANCE = new NullLabeling();
	}

	private NullLabeling() {
	}

	public static NullLabeling getInstance() {
		return INSTANCE;
	}

	@Override
	public Void getLabelForInitNode(final ARGNode<? extends State, Void, Void> initNode, final Object init,
			final Object target) {
		return null;
	}

	@Override
	public Product2<Void, Void> getLabelForSuccNode(final ARGNode<? extends State, Void, Void> succNode,
			final Object trans, final Object target) {
		return null;
	}

}
