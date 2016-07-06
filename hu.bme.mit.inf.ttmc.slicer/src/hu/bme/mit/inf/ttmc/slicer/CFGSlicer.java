package hu.bme.mit.inf.ttmc.slicer;

import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;

public interface CFGSlicer {

	public CFG slice(CFG input, CFGNode criteria);

}
