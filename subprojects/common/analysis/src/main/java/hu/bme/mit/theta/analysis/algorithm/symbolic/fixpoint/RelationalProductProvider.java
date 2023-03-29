package hu.bme.mit.theta.analysis.algorithm.symbolic.fixpoint;

import hu.bme.mit.delta.java.mdd.Cache;
import hu.bme.mit.delta.java.mdd.MddTransformationProvider;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.AbstractNextStateDescriptor;

public interface RelationalProductProvider extends MddTransformationProvider<AbstractNextStateDescriptor> {

    Cache getRelProdCache();

}
