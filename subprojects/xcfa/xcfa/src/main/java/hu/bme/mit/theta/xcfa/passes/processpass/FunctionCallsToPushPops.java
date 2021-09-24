package hu.bme.mit.theta.xcfa.passes.processpass;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.PopStmt;
import hu.bme.mit.theta.core.stmt.PushStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.xcfa.model.XcfaProcedure.Direction.IN;
import static hu.bme.mit.theta.xcfa.model.XcfaProcedure.Direction.OUT;

public class FunctionCallsToPushPops extends ProcessPass{
	private static int counter = 0;
	@Override
	public XcfaProcess.Builder run(XcfaProcess.Builder builder) {
		if(builder.getProcedures().size() <= 1) return builder;
		final XcfaProcedure.Builder mainProcedure = builder.getMainProcedure();

		final VarDecl<Type> retVar = Var("ret", CComplexType.getUnsignedLong().getSmtType());
		mainProcedure.createVar(retVar, null);
		FrontendMetadata.create(retVar.getRef(), "cType", CComplexType.getUnsignedLong());

		final Map<XcfaProcedure.Builder, Map<XcfaLocation, XcfaLocation>> alreadyHandled = new LinkedHashMap<>();
		final List<XcfaLocation> callSites = new ArrayList<>();

		alreadyHandled.put(mainProcedure, mainProcedure.getLocs().stream().map(xcfaLocation -> Map.entry(xcfaLocation, xcfaLocation)).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue)));
		boolean found = true;
		while(found) {
			found = false;

			for (XcfaEdge edge : new ArrayList<>(mainProcedure.getEdges())) {
				final List<XcfaLabel> labels = edge.getLabels();
				for (int i = 0; i < labels.size(); i++) {
					final XcfaLabel label = labels.get(i);
					if (label instanceof XcfaLabel.ProcedureCallXcfaLabel) {
						found = true;
						mainProcedure.removeEdge(edge);
						XcfaLocation source = edge.getSource();
						XcfaLocation target = edge.getTarget();
						if (i > 0) {
							source = XcfaLocation.create("__tmp" + XcfaLocation.uniqeCounter());
							mainProcedure.addLoc(source);
							mainProcedure.addEdge(XcfaEdge.of(edge.getSource(), source, labels.subList(0, i)));
						}
						if (labels.size() > i + 1) {
							target = XcfaLocation.create("__tmp" + XcfaLocation.uniqeCounter());
							mainProcedure.addLoc(target);
							mainProcedure.addEdge(XcfaEdge.of(target, edge.getTarget(), labels.subList(i+1, labels.size())));
						}
						final int index = callSites.size();
						callSites.add(target);

						final String procedureName = ((XcfaLabel.ProcedureCallXcfaLabel) label).getProcedure();
						final Optional<XcfaProcedure.Builder> procedureOpt = builder.getProcedures().stream().filter(builder1 -> builder1.getName().equals(procedureName)).findFirst();
						checkState(procedureOpt.isPresent(), "No such procedure " + procedureName);
						final XcfaProcedure.Builder procedure = procedureOpt.get();
						if(!alreadyHandled.containsKey(procedure)) {
							final Map<XcfaLocation, XcfaLocation> locationLut = new LinkedHashMap<>();
							alreadyHandled.put(procedure, locationLut);
							procedure.getParams().forEach((varDecl, direction) -> mainProcedure.createVar(varDecl, null));
							procedure.getLocalVars().forEach((varDecl, litExpr) -> mainProcedure.createVar(varDecl, litExpr.orElse(null)));
							for (XcfaLocation xcfaLocation : procedure.getLocs()) {
								final XcfaLocation newLocation = XcfaLocation.uniqeCopyOf(xcfaLocation);
								locationLut.put(xcfaLocation, newLocation);
								mainProcedure.addLoc(newLocation);
							}
							procedure.getEdges().forEach(xcfaEdge -> mainProcedure.addEdge(XcfaEdge.of(locationLut.get(xcfaEdge.getSource()), locationLut.get(xcfaEdge.getTarget()), xcfaEdge.getLabels())));
							final XcfaLocation newErrorLoc = locationLut.get(procedure.getErrorLoc());
							if(newErrorLoc != null) {
								if (mainProcedure.getErrorLoc() == null) {
									mainProcedure.setErrorLoc(newErrorLoc);
								} else {
									mainProcedure.addEdge(XcfaEdge.of(newErrorLoc, mainProcedure.getErrorLoc(), List.of()));
								}
							}
						}


						final Iterator<Map.Entry<VarDecl<?>, XcfaProcedure.Direction>> it = procedure.getParams().entrySet().iterator();
						final List<XcfaLabel> inLabels = new ArrayList<>();
						inLabels.add(XcfaLabel.Stmt(Assign(retVar, cast(CComplexType.getUnsignedLong().getValue("" + index), retVar.getType()))));
						final List<XcfaLabel> outLabels = new ArrayList<>();
						outLabels.add(XcfaLabel.Stmt(Assume(Eq(retVar.getRef(), cast(CComplexType.getUnsignedLong().getValue("" + index), retVar.getType())))));
						for (VarDecl<?> varDecl : procedure.getLocalVars().keySet()) {
							if(varDecl != retVar) outLabels.add(XcfaLabel.Stmt(PopStmt.of(varDecl)));
						}
						for (Expr<?> paramExpr : ((XcfaLabel.ProcedureCallXcfaLabel) label).getParams()) {
							final Map.Entry<VarDecl<?>, XcfaProcedure.Direction> paramVar = it.next();
							inLabels.add(XcfaLabel.Stmt(PushStmt.of(paramVar.getKey())));
							if(paramVar.getValue() != OUT) inLabels.add(XcfaLabel.Stmt(Assign(cast(paramVar.getKey(), paramVar.getKey().getType()), cast(paramExpr, paramVar.getKey().getType()))));
							if(paramVar.getValue() != IN) {
								checkState(paramExpr instanceof RefExpr<?>);
								final VarDecl<?> outVar = (VarDecl<?>) ((RefExpr<?>) paramExpr).getDecl();
								outLabels.add(XcfaLabel.Stmt(Assign(cast(outVar, outVar.getType()), cast(paramVar.getKey().getRef(), outVar.getType()))));
							}
							outLabels.add(XcfaLabel.Stmt(PopStmt.of(paramVar.getKey())));
						}
						for (VarDecl<?> varDecl : procedure.getLocalVars().keySet()) {
							if(varDecl != retVar) inLabels.add(XcfaLabel.Stmt(PushStmt.of(varDecl)));
						}
						mainProcedure.addEdge(XcfaEdge.of(source, alreadyHandled.get(procedure).get(procedure.getInitLoc()), inLabels));
						mainProcedure.addEdge(XcfaEdge.of(alreadyHandled.get(procedure).get(procedure.getFinalLoc()), target, outLabels));
						break;
					}
				}
			}
		}
//		builder.getProcedures().removeIf(builder1 -> builder1 != mainProcedure);
		return builder;
	}
}
