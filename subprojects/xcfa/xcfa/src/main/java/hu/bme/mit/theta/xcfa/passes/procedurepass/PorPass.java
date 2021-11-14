package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.utils.LabelUtils;

import java.util.ArrayList;
import java.util.List;

public class PorPass extends ProcedurePass{
	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		if(!ArchitectureConfig.multiThreading) return builder;
		for (XcfaEdge edge : new ArrayList<>(builder.getEdges())) {
			List<XcfaLabel> newLabels = new ArrayList<>();
			boolean removed = false;
			XcfaLocation source = edge.getSource();
			for (XcfaLabel label : edge.getLabels()) {
				if(LabelUtils.isNotLocal(label, builder.getLocalVars())) {
					if(!removed) {
						builder.removeEdge(edge);
						removed = true;
					}
					if(newLabels.size() > 0) {
						XcfaLocation tmp = XcfaLocation.create("tmp" + XcfaLocation.uniqeCounter());
						builder.addLoc(tmp);
						builder.addEdge(edge.withSource(source).withLabels(newLabels).withTarget(tmp));
						source = tmp;
						newLabels.clear();
					}
					XcfaLocation tmp = XcfaLocation.create("tmp" + XcfaLocation.uniqeCounter());
					builder.addLoc(tmp);
					builder.addEdge(edge.withSource(source).withLabels(List.of(label)).withTarget(tmp));
					source = tmp;
				} else {
					newLabels.add(label);
				}
			}
			if(removed) {
				builder.addEdge(edge.withSource(source).withLabels(newLabels).withTarget(edge.getTarget()));
			}
		}
		return builder;
	}

	@Override
	public boolean isPostInlining() {
		return true;
	}
}