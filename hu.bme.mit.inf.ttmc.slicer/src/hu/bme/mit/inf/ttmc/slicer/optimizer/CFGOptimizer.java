package hu.bme.mit.inf.ttmc.slicer.optimizer;

import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;

public interface CFGOptimizer {

	public CFG transform(CFG input);

}
