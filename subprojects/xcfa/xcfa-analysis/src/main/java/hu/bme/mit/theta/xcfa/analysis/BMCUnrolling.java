package hu.bme.mit.theta.xcfa.analysis;

import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.passes.procedurepass.UnrollLoopsPass;

import java.util.List;

import static hu.bme.mit.theta.xcfa.passes.procedurepass.Utils.collectPaths;
import static hu.bme.mit.theta.xcfa.passes.procedurepass.Utils.createBuilder;

public class BMCUnrolling {
	private static final int MAX_K = 5000;

	public List<XcfaEdge> getCex(XcfaProcedure builder) {
		if(builder.getErrorLoc() == null) return null;

		XcfaProcedure.Builder workingCopy = createBuilder(builder);
		UnrollLoopsPass unrollLoopsPass = new UnrollLoopsPass();

		for(int i = 0; i < MAX_K; ++i) {
			List<XcfaEdge> cex;
			if((cex = getCex(workingCopy)) != null) {
				return cex;
			}
			System.out.println("BMC has not found a violation in iteration " + i + " with " + workingCopy.getEdges().size() + " edges.");
			workingCopy = unrollLoopsPass.run(workingCopy);
		}

		return null;
	}

	private List<XcfaEdge> getCex(XcfaProcedure.Builder builder) {
		XcfaLocation initLoc = builder.getInitLoc();
		XcfaLocation errorLoc = builder.getErrorLoc();
		return collectPaths(initLoc, errorLoc);
	}
}
