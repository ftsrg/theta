package hu.bme.mit.theta.xcfa.passes.processpass;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.xcfa.model.*;

import java.util.*;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.Stmt;

public class AssignFunctionParam extends ProcessPass {
	private final List<XcfaEdge> edgesToAdd = new ArrayList<>();
	private final List<XcfaEdge> edgesToRemove = new ArrayList<>();
	private final Map<XcfaProcedure.Builder, Set<XcfaLabel.ProcedureCallXcfaLabel>> procedureCalls = new LinkedHashMap<>();

	@Override
	public XcfaProcess.Builder run(XcfaProcess.Builder builder) {
		for (XcfaProcedure.Builder procedure : builder.getProcedures()) {
			edgesToAdd.clear();
			edgesToRemove.clear();
			procedureCalls.clear();
			for (XcfaEdge edge : procedure.getEdges()) {
				for (XcfaLabel label : edge.getLabels()) {
					if (label instanceof XcfaLabel.ProcedureCallXcfaLabel) {
						XcfaLabel.ProcedureCallXcfaLabel callLabel = (XcfaLabel.ProcedureCallXcfaLabel) label;
						Optional<XcfaProcedure.Builder> procedureOpt = builder.getProcedures().stream().filter(xcfaProcedure -> xcfaProcedure.getName().equals(callLabel.getProcedure())).findAny();
						procedureOpt.ifPresent(calledProcedure -> {
							assignParams(callLabel, calledProcedure);
							if (calledProcedure.getRetType() != null) {
								List<XcfaLabel> retStmts = getRetStmts(callLabel, calledProcedure);
								assignReturns(procedure, edge, retStmts);
							}
						});
					}
				}
			}
			edgesToRemove.forEach(procedure::removeEdge);
			edgesToAdd.forEach(procedure::addEdge);
			procedureCalls.forEach((calledProcedure, callLabels) -> callLabels.forEach(calledProcedure::addParamInitLoc));
		}
		return builder;
	}

	private void assignParams(XcfaLabel.ProcedureCallXcfaLabel callLabel, XcfaProcedure.Builder calledProcedure) {
		Set<XcfaLabel.ProcedureCallXcfaLabel> callLabels = procedureCalls.getOrDefault(calledProcedure, new HashSet<>());
		callLabels.add(callLabel);
		procedureCalls.put(calledProcedure, callLabels);
	}

	private void assignReturns(XcfaProcedure.Builder procedure, XcfaEdge edge, List<XcfaLabel> retStmts) {
		XcfaLocation middle = XcfaLocation.uniqeCopyOf(edge.getSource());
		procedure.addLoc(middle);
		edgesToRemove.add(edge);
		edgesToAdd.add(XcfaEdge.of(edge.getSource(), middle, edge.getLabels()));
		XcfaEdge retEdge = XcfaEdge.of(middle, edge.getTarget(), retStmts);
		FrontendMetadata.lookupMetadata(edge).forEach((s, o) -> FrontendMetadata.create(retEdge, s, o));
		edgesToAdd.add(retEdge);
	}

	private List<XcfaLabel> getRetStmts(XcfaLabel.ProcedureCallXcfaLabel callLabel, XcfaProcedure.Builder calledProcedure) {
		List<XcfaLabel> retStmts = new ArrayList<>();
		int paramCnt = 0;
		for (Map.Entry<VarDecl<?>, XcfaProcedure.Direction> entry : calledProcedure.getParams().entrySet()) {
			VarDecl<?> varDecl = entry.getKey();
			XcfaProcedure.Direction direction = entry.getValue();
			if (direction != XcfaProcedure.Direction.IN) {
				Expr<?> expr = callLabel.getParams().get(paramCnt);
				checkState(expr instanceof RefExpr && ((RefExpr<?>) expr).getDecl() instanceof VarDecl<?>);
				retStmts.add(Stmt(Assign(cast((VarDecl<?>) ((RefExpr<?>) expr).getDecl(), varDecl.getType()), cast(varDecl.getRef(), varDecl.getType()))));
			}
			++paramCnt;
		}
		return retStmts;
	}
}
