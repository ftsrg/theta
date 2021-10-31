package hu.bme.mit.theta.xcfa.passes.processpass;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.frontend.transformation.grammar.expression.Reference;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;
import hu.bme.mit.theta.xcfa.passes.XcfaPassManager;
import hu.bme.mit.theta.xcfa.passes.procedurepass.ProcedurePass;
import hu.bme.mit.theta.xcfa.passes.procedurepass.UnusedVarRemovalPass;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.Stmt;
import static hu.bme.mit.theta.xcfa.passes.procedurepass.Utils.getNonModifiedVars;

public class FunctionInlining extends ProcessPass {
	private final List<String> nopFuncs = List.of("reach_error", "abort");
	private final Set<Tuple2<XcfaLabel, XcfaEdge>> alreadyHandled = new LinkedHashSet<>();

	@Override
	public XcfaProcess.Builder run(XcfaProcess.Builder builder) {
		ProcedurePass.postInlining = true;
		XcfaProcess.Builder newBuilder = XcfaProcess.builder();
		newBuilder.setName(builder.getName());
		newBuilder.getThreadLocalVars().putAll(builder.getThreadLocalVars());
		for (VarDecl<?> param : builder.getParams()) {
			newBuilder.createParam(param);
		}
		Set<VarDecl<?>> usedVars = new LinkedHashSet<>();

		XcfaProcedure.Builder mainProcedure = builder.getMainProcedure();
		alreadyHandled.clear();
		XcfaProcedure.Builder newMainProc = inlineProcedure(builder, newBuilder, mainProcedure);

		Set<XcfaProcedure.Builder> alreadyInlined = new LinkedHashSet<>();
		alreadyInlined.add(newMainProc);

		for (final Object shouldKeepObj : FrontendMetadata.lookupMetadata("shouldKeep", true)) {
			checkState(shouldKeepObj instanceof XcfaProcedure.Builder, "Bad shouldKeep metadata!");
			final XcfaProcedure.Builder shouldKeep = (XcfaProcedure.Builder) shouldKeepObj;
			alreadyInlined.add(inlineProcedure(builder, newBuilder, shouldKeep));
		}

		for (XcfaProcedure.Builder procedure : alreadyInlined) {
			for (XcfaEdge edge : procedure.getEdges()) {
				for (XcfaLabel label : edge.getLabels()) {
					usedVars.addAll(getNonModifiedVars(label));
				}
			}
		}

		for (XcfaProcedure.Builder procBuilder : alreadyInlined) {
			UnusedVarRemovalPass.removeUnusedVars(procBuilder, usedVars);
			newBuilder.addProcedure(XcfaPassManager.run(procBuilder));
			if(procBuilder == newMainProc) newBuilder.setMainProcedure(procBuilder);
		}

		FrontendMetadata.lookupMetadata("shouldInline", false).stream().filter(o -> o instanceof XcfaProcedure.Builder).map(o -> (XcfaProcedure.Builder)o).forEach(procedure -> newBuilder.addProcedure(XcfaPassManager.run(procedure)));

		return newBuilder;

	}

	private XcfaProcedure.Builder inlineProcedure(XcfaProcess.Builder builder, XcfaProcess.Builder newBuilder, XcfaProcedure.Builder procedure) {
		//		mainProcBuilder.setErrorLoc(mainProcedure.getErrorLoc());
		Map<XcfaEdge, List<XcfaLabel.ProcedureCallXcfaLabel>> splittingPoints = new LinkedHashMap<>();


		while(handleCallStmts(builder, procedure, splittingPoints)) {
			splitAndInlineEdges(builder, procedure, splittingPoints);
			splittingPoints.clear();
		}
		truncateAssignments(builder, procedure);

		return procedure;
	}

	/**
	 * In assignments we need to convert the C type of the right hand expression to the C type of the left one.
	 * In the case, where the left type is smaller in maximum size than the right one, we'll truncate the value.
	 * We need to add a modulo to the right expression in this case to truncate.
	 */
	private void truncateAssignments(XcfaProcess.Builder builder, XcfaProcedure.Builder procBuilder) {
		List<XcfaEdge> edgesCopy = new ArrayList<>(procBuilder.getEdges());
		for (XcfaEdge edge : edgesCopy) {
			boolean atLeastOneAssignmentTruncated = false;
			List<XcfaLabel> newStmts = new ArrayList<>(edge.getLabels());
			for (XcfaLabel label : edge.getLabels()) {
				if (label instanceof XcfaLabel.StmtXcfaLabel && label.getStmt() instanceof AssignStmt && !(((AssignStmt<?>) label.getStmt()).getVarDecl().getType() instanceof ArrayType)) {
					AssignStmt<?> assignStmt = (AssignStmt<?>) label.getStmt();
					CComplexType leftType = CComplexType.getType(assignStmt.getVarDecl().getRef());
					checkNotNull(leftType);
					Expr<?> expr = assignStmt.getExpr();

					Expr<?> truncatedExpr = leftType.castTo(expr);
					FrontendMetadata.create(truncatedExpr, "cType", leftType);
					if (!expr.equals(truncatedExpr)) {
						atLeastOneAssignmentTruncated = true;
						newStmts.remove(label);
						AssignStmt<?> newStmt = Assign(cast(assignStmt.getVarDecl(), assignStmt.getVarDecl().getType()), cast(truncatedExpr, assignStmt.getVarDecl().getType()));
						newStmts.add(Stmt(newStmt));
					}
				}
			}
			if (atLeastOneAssignmentTruncated) {
				XcfaEdge newEdge = XcfaEdge.of(edge.getSource(), edge.getTarget(), newStmts);
				FrontendMetadata.lookupMetadata(edge).forEach((s, o) -> {
					FrontendMetadata.create(newEdge, s, o);
				});
				procBuilder.removeEdge(edge);
				procBuilder.addEdge(newEdge);
			}
		}


	}

	private void splitAndInlineEdges(XcfaProcess.Builder oldBuilder, XcfaProcedure.Builder procBuilder, Map<XcfaEdge, List<XcfaLabel.ProcedureCallXcfaLabel>> splittingPoints) {
		splittingPoints.forEach((xcfaEdge, xcfaCallStmts) -> {
			procBuilder.removeEdge(xcfaEdge);
			XcfaLabel.ProcedureCallXcfaLabel xcfaCallStmt = xcfaCallStmts.get(0);
			int i = xcfaEdge.getLabels().indexOf(xcfaCallStmt);
			XcfaLocation start = xcfaEdge.getSource();
			XcfaLocation end = xcfaEdge.getTarget();
			if(i > 0) {
				XcfaLocation loc1 = XcfaLocation.create("inline" + XcfaLocation.uniqeCounter());
				FrontendMetadata.lookupMetadata(xcfaEdge).forEach((s, o) -> {
					FrontendMetadata.create(loc1, s, o);
				});
				procBuilder.addLoc(loc1);
				XcfaEdge edge = XcfaEdge.of(start, loc1, sublist(xcfaEdge.getLabels(), 0, i));
				procBuilder.addEdge(edge);
				FrontendMetadata.lookupMetadata(xcfaEdge).forEach((s, o) -> {
					FrontendMetadata.create(edge, s, o);
				});
				start = loc1;
			}
			if(i < xcfaEdge.getLabels().size() - 1) {
				XcfaLocation loc1 = XcfaLocation.create("inline" + XcfaLocation.uniqeCounter());
				FrontendMetadata.lookupMetadata(xcfaEdge).forEach((s, o) -> {
					FrontendMetadata.create(loc1, s, o);
				});
				procBuilder.addLoc(loc1);
				XcfaEdge edge = XcfaEdge.of(loc1, end, sublist(xcfaEdge.getLabels(), i + 1, xcfaEdge.getLabels().size()));
				procBuilder.addEdge(edge);
				FrontendMetadata.lookupMetadata(xcfaEdge).forEach((s, o) -> {
					FrontendMetadata.create(edge, s, o);
				});
				end = loc1;
			}
			Optional<XcfaProcedure.Builder> procedureOpt = oldBuilder.getProcedures().stream().filter(xcfaProcedure -> xcfaProcedure.getName().equals(xcfaCallStmt.getProcedure())).findAny();
			checkState(procedureOpt.isPresent());
			XcfaProcedure.Builder procedure = procedureOpt.get();
			for (VarDecl<?> localVar : procedure.getLocalVars().keySet()) {
				checkState(procedure.getLocalVars().get(localVar).isEmpty(), "Non-global variable should not have a starting expression!");
				procBuilder.createVar(localVar, null);
			}
			procedure.getParams().forEach((varDecl, direction) -> procBuilder.createVar(varDecl, null));
			Map<XcfaLocation, XcfaLocation> locationLut = new LinkedHashMap<>();
			procedure.getLocs().forEach(loc -> {
				XcfaLocation copy = XcfaLocation.uniqeCopyOf(loc);
				locationLut.put(loc, copy);
				procBuilder.addLoc(copy);
			});
			procedure.getEdges().forEach(e -> procBuilder.addEdge(XcfaEdge.of(locationLut.get(e.getSource()), locationLut.get(e.getTarget()), e.getLabels())));
			procedure.getFinalLoc().setEndLoc(false);

			int paramCnt = 0;
			List<XcfaLabel> retStmts = new ArrayList<>();
			List<XcfaLabel> initStmts = new ArrayList<>();
			for (Map.Entry<VarDecl<?>, XcfaProcedure.Direction> entry : procedure.getParams().entrySet()) {
				VarDecl<?> varDecl = entry.getKey();
				XcfaProcedure.Direction direction = entry.getValue();
				if (direction != XcfaProcedure.Direction.OUT) {
					CComplexType funcParamType = CComplexType.getType(varDecl.getRef());
					checkNotNull(funcParamType);
					Expr<?> param = xcfaCallStmt.getParams().get(paramCnt);
					Expr<?> truncatedParam = funcParamType.castTo(param);
					FrontendMetadata.create(truncatedParam, "cType", funcParamType);

					AssignStmt<?> assignStmt = Assign(cast(varDecl, varDecl.getType()), cast(truncatedParam, varDecl.getType()));
					initStmts.add(Stmt(assignStmt));
					if (truncatedParam instanceof Reference) {
						Optional<Object> pointsTo = FrontendMetadata.getMetadataValue(varDecl.getRef(), "pointsTo");
						if(pointsTo.isPresent() && pointsTo.get() instanceof Collection) {
							((Collection<Expr<?>>) pointsTo.get()).add(((Reference<?, ?>) truncatedParam).getOp());
						} else {
							pointsTo = Optional.of(new LinkedHashSet<Expr<?>>(Set.of(((Reference<?, ?>) truncatedParam).getOp())));
						}
						FrontendMetadata.create(varDecl.getRef(), "pointsTo", pointsTo.get());
					}
				}
				if (direction != XcfaProcedure.Direction.IN) {
					Expr<?> expr = xcfaCallStmt.getParams().get(paramCnt);
					checkState(expr instanceof RefExpr && ((RefExpr<?>) expr).getDecl() instanceof VarDecl<?>);
					retStmts.add(Stmt(Assign(cast((VarDecl<?>) ((RefExpr<?>) expr).getDecl(), varDecl.getType()), cast(varDecl.getRef(), varDecl.getType()))));
				}
				++paramCnt;
			}
			XcfaEdge xcfaEdge1 = XcfaEdge.of(start, locationLut.get(procedure.getInitLoc()), initStmts);
			FrontendMetadata.lookupMetadata(xcfaEdge).forEach((s, o) -> {
				FrontendMetadata.create(xcfaEdge1, s, o);
			});
			XcfaEdge xcfaEdge2 = XcfaEdge.of(locationLut.get(procedure.getFinalLoc()), end, retStmts);
			FrontendMetadata.lookupMetadata(xcfaEdge).forEach((s, o) -> {
				FrontendMetadata.create(xcfaEdge2, s, o);
			});
			procBuilder.addEdge(xcfaEdge1);
			procBuilder.addEdge(xcfaEdge2);
		});
	}

	private List<XcfaLabel> sublist(List<XcfaLabel> labels, int from, int to) {
		List<XcfaLabel> ret = new ArrayList<>();
		for (int i = 0; i < labels.size(); i++) {
			if(i >= from && i < to) ret.add(labels.get(i));
		}
		return ret;
	}


	private boolean handleCallStmts(XcfaProcess.Builder builder, XcfaProcedure.Builder mainProcBuilder, Map<XcfaEdge, List<XcfaLabel.ProcedureCallXcfaLabel>> splittingPoints) {
		boolean anyMatch = false;
		for (XcfaEdge edge : mainProcBuilder.getEdges()) {
			boolean stillExists = true;
			while(stillExists) {
				Optional<XcfaLabel> callStmtOpt = edge.getLabels().stream().filter(stmt ->
						stmt instanceof XcfaLabel.ProcedureCallXcfaLabel &&
						!alreadyHandled.contains(Tuple2.of(stmt, edge)) &&
						!nopFuncs.contains(((XcfaLabel.ProcedureCallXcfaLabel)stmt).getProcedure()) &&
						shouldInlineCall(builder, (XcfaLabel.ProcedureCallXcfaLabel) stmt)).findAny();
				if(callStmtOpt.isPresent() ) {
					alreadyHandled.add(Tuple2.of(callStmtOpt.get(), edge));
					anyMatch = true;
					Optional<XcfaProcedure.Builder> procedure = builder.getProcedures().stream().filter(xcfaProcedure -> xcfaProcedure.getName().equals(((XcfaLabel.ProcedureCallXcfaLabel) callStmtOpt.get()).getProcedure())).findAny();
					if (procedure.isPresent()) {
						splittingPoints.putIfAbsent(edge, new ArrayList<>());
						splittingPoints.get(edge).add((XcfaLabel.ProcedureCallXcfaLabel) callStmtOpt.get());
					}
				} else {
					stillExists = false;
				}
			}
		}
		return anyMatch;
	}

	private boolean shouldInlineCall(XcfaProcess.Builder builder, XcfaLabel.ProcedureCallXcfaLabel callStmt) {
		Optional<XcfaProcedure.Builder> procedure = builder.getProcedures().stream().filter(xcfaProcedure -> xcfaProcedure.getName().equals(callStmt.getProcedure())).findAny();
		if(procedure.isPresent()) {
			Optional<Object> shouldInlineProc = FrontendMetadata.getMetadataValue(procedure.get(), "shouldInline");
			if(shouldInlineProc.isPresent() && shouldInlineProc.get() instanceof Boolean) {
				return (Boolean) shouldInlineProc.get();
			}
			Optional<Object> shouldInline = FrontendMetadata.getMetadataValue(procedure.get().getName(), "shouldInline");
			return shouldInline.isEmpty() || !(shouldInline.get() instanceof Boolean) || (Boolean) shouldInline.get();
		}
		return true;
	}
}
