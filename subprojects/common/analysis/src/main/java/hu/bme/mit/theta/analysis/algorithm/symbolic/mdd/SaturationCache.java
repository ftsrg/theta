package hu.bme.mit.theta.analysis.algorithm.symbolic.mdd;

import hu.bme.mit.delta.java.mdd.BinaryOperationCache;
import hu.bme.mit.delta.java.mdd.Cache;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.TernaryOperationCache;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.AbstractNextStateDescriptor;

public final class SaturationCache implements Cache {
	private final BinaryOperationCache<MddNode, AbstractNextStateDescriptor, MddNode>                               saturateCache = new BinaryOperationCache<>();
	private final TernaryOperationCache<MddNode, AbstractNextStateDescriptor, AbstractNextStateDescriptor, MddNode> relProdCache  = new TernaryOperationCache<>();
	
	public BinaryOperationCache<MddNode, AbstractNextStateDescriptor, MddNode> getSaturateCache() {
		return saturateCache;
	}
	
	public TernaryOperationCache<MddNode, AbstractNextStateDescriptor, AbstractNextStateDescriptor, MddNode> getRelProdCache() {
		return relProdCache;
	}
	
	@Override
	public void clear() {
		saturateCache.clear();
		relProdCache.clear();
	}
	
	@Override
	public long getCacheSize() {
		return saturateCache.getCacheSize() + relProdCache.getCacheSize();
	}
	
	@Override
	public long getQueryCount() {
		return saturateCache.getQueryCount() + relProdCache.getQueryCount();
	}
	
	@Override
	public long getHitCount() {
		return saturateCache.getHitCount() + relProdCache.getHitCount();
	}
}
