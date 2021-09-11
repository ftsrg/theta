package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class SimpleLbePass extends ProcedurePass{
	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		builder = EliminateSelfLoops.instance.run(builder);
		Set<XcfaLocation> pathlocs = builder.getLocs().stream().filter(xcfaLocation -> xcfaLocation.getIncomingEdges().size() == 1 && xcfaLocation.getOutgoingEdges().size() == 1).collect(Collectors.toSet());
		for (XcfaLocation pathloc : pathlocs) {
			XcfaEdge inEdge = pathloc.getIncomingEdges().get(0);
			XcfaEdge outEdge = pathloc.getOutgoingEdges().get(0);

			builder.removeEdge(inEdge);
			builder.removeEdge(outEdge);
			builder.removeLoc(pathloc);

			List<Stmt> stmts = new ArrayList<>(inEdge.getLabels());
			stmts.addAll(outEdge.getLabels());

			builder.addEdge(XcfaEdge.of(inEdge.getSource(), outEdge.getTarget(), stmts));
		}
		return builder;
	}

	@Override
	public boolean isPostInlining() {
		return true;
	}
}
