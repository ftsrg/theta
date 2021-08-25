package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.List;

import static hu.bme.mit.theta.xcfa.passes.procedurepass.Utils.collectPaths;
import static hu.bme.mit.theta.xcfa.passes.procedurepass.Utils.createBuilder;

public class BMC{
	private static final int MAX_K = 100;

	public List<XcfaEdge> getCex(XcfaProcedure builder) {
		if(builder.getErrorLoc() == null) return null;

		XcfaProcedure.Builder workingCopy = createBuilder(builder);
		UnrollLoopsPass unrollLoopsPass = new UnrollLoopsPass();

		for(int i = 0; i < MAX_K; ++i) {
			List<XcfaEdge> cex;
			if((cex = getCex(workingCopy)) != null) {
				return cex;
//				XcfaProcedure.Builder retBuilder = XcfaProcedure.builder();
//				retBuilder.setName(builder.getName());
//				Map<XcfaLocation, XcfaLocation> locLut = new LinkedHashMap<>();
//				for (XcfaEdge edge : cex) {
//					XcfaLocation source = edge.getSource();
//					XcfaLocation target = edge.getTarget();
//					XcfaLocation newSource = XcfaLocation.copyOf(source);
//					XcfaLocation newTarget = XcfaLocation.copyOf(target);
//					locLut.putIfAbsent(source, newSource);
//					locLut.putIfAbsent(target, newTarget);
//					newSource = locLut.get(source);
//					newTarget = locLut.get(target);
//					retBuilder.addLoc(newSource);
//					retBuilder.addLoc(newTarget);
//					retBuilder.addEdge(new XcfaEdge(newSource, newTarget, edge.getStmts()));
//				}
//				retBuilder.setInitLoc(locLut.get(workingCopy.getInitLoc()));
//				XcfaLocation location = new XcfaLocation("final", Map.of()); // Final location never contained in CEX but still necesaary
//				retBuilder.addLoc(location);
//				retBuilder.setFinalLoc(location);
//				retBuilder.setErrorLoc(locLut.get(workingCopy.getErrorLoc()));
//				System.err.println("BMC saves the day!");
//				return retBuilder.build();
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
