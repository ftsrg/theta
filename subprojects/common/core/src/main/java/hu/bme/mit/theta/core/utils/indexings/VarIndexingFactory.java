package hu.bme.mit.theta.core.utils.indexings;

public class VarIndexingFactory {

	public static PushPopVarIndexing pushPopIndexing(final int defaultOffset) {
		return PushPopVarIndexing.all(defaultOffset);
	}

	public static BasicVarIndexing basicVarIndexing(final int defaultOffset) {
		return BasicVarIndexing.all(defaultOffset);
	}

	public static VarIndexing indexing(final int defaultOffset) {
		return basicVarIndexing(defaultOffset);
	}

	public static PushPopVarIndexing.PushPopVarIndexingBuilder pushPopIndexingBuilder(final int defaultOffset) {
		return PushPopVarIndexing.builder(defaultOffset);
	}

	public static BasicVarIndexing.BasicVarIndexingBuilder basicIndexingBuilder(final int defaultOffset) {
		return BasicVarIndexing.builder(defaultOffset);
	}

	public static VarIndexingBuilder indexingBuilder(final int defaultOffset) {
		return basicIndexingBuilder(defaultOffset);
	}
}
