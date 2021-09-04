package hu.bme.mit.theta.xcfa.passes.processpass;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.xcfa.StartThreadStmt;
import hu.bme.mit.theta.core.stmt.xcfa.StoreStmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaCallStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;
import hu.bme.mit.theta.xcfa.passes.procedurepass.ProcedurePass;
import hu.bme.mit.theta.xcfa.passes.procedurepass.UnusedVarRemovalPass;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;

import java.util.ArrayList;
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
import static hu.bme.mit.theta.xcfa.passes.procedurepass.Utils.createBuilder;

public class FunctionInlining extends ProcessPass {
	private int counter = 0;
	private final List<String> nopFuncs = List.of("reach_error", "abort");
	private final Set<Tuple2<Stmt, XcfaEdge>> alreadyHandled = new LinkedHashSet<>();

	@Override
	public XcfaProcess.Builder run(XcfaProcess.Builder builder) {
		ProcedurePass.postInlining = true;
		alreadyHandled.clear();
		XcfaProcess.Builder newBuilder = XcfaProcess.builder();
		newBuilder.setName(builder.getName());
		newBuilder.getThreadLocalVars().putAll(builder.getThreadLocalVars());
		for (VarDecl<?> param : builder.getParams()) {
			newBuilder.createParam(param);
		}
		XcfaProcedure mainProcedure = builder.getMainProcedure();
		XcfaProcedure.Builder newMainProc = inlineProcedure(builder, newBuilder, mainProcedure);

		Set<XcfaProcedure.Builder> alreadyInlined = new LinkedHashSet<>();
		alreadyInlined.add(newMainProc);
		boolean foundOne = true;
		while(foundOne) {
			foundOne = false;
			for (XcfaProcedure.Builder procedure : new ArrayList<>(alreadyInlined)) {
				for (XcfaEdge edge : procedure.getEdges()) {
					for (Stmt stmt : edge.getStmts()) {
						if(stmt instanceof StartThreadStmt) {
							String threadName = ((StartThreadStmt) stmt).getThreadName();
							Optional<XcfaProcedure.Builder> func = alreadyInlined.stream().filter(xcfaProcedure -> xcfaProcedure.getName().equals(threadName)).findAny();
							if(func.isEmpty()) {
								Optional<XcfaProcedure> oldProc = builder.getProcedures().stream().filter(xcfaProcedure -> xcfaProcedure.getName().equals(threadName)).findAny();
								if(oldProc.isPresent()) {
									foundOne = true;
									XcfaProcedure.Builder builder1 = inlineProcedure(builder, newBuilder, oldProc.get());
									alreadyInlined.add(builder1);
								}
							}
						}
					}
				}
			}
		}

		Set<VarDecl<?>> usedVars = new LinkedHashSet<>();
		for (XcfaProcedure.Builder procedure : alreadyInlined) {
			for (XcfaEdge edge : procedure.getEdges()) {
				for (Stmt stmt : edge.getStmts()) {
					if (stmt instanceof AssignStmt) {
						usedVars.addAll(ExprUtils.getVars(((AssignStmt<?>) stmt).getExpr()));
					} else if (stmt instanceof StoreStmt){
						usedVars.add(((StoreStmt) stmt).getLocal());
					}
					else {
						usedVars.addAll(StmtUtils.getVars(stmt));
					}
				}
			}
		}

		for (XcfaProcedure.Builder procBuilder : alreadyInlined) {
			UnusedVarRemovalPass.removeUnusedVars(procBuilder, usedVars);
			XcfaProcedure procedure = procBuilder.build();
			newBuilder.addProcedure(procedure);
			if(procBuilder == newMainProc) newBuilder.setMainProcedure(procedure);
		}

		FrontendMetadata.lookupMetadata("shouldInline", false).stream().filter(o -> o instanceof XcfaProcedure).map(o -> (XcfaProcedure)o).forEach(newBuilder::addProcedure);

		return newBuilder;

	}

	private XcfaProcedure.Builder inlineProcedure(XcfaProcess.Builder builder, XcfaProcess.Builder newBuilder, XcfaProcedure procedure) {
		XcfaProcedure.Builder procBuilder = createBuilder(procedure);
//		mainProcBuilder.setErrorLoc(mainProcedure.getErrorLoc());
		Map<XcfaEdge, List<XcfaCallStmt>> splittingPoints = new LinkedHashMap<>();


		while(handleCallStmts(builder, procedure, procBuilder, splittingPoints)) {
			splitAndInlineEdges(builder, procBuilder, splittingPoints);
			splittingPoints.clear();
		}
		truncateAssignments(builder, procBuilder);

		return procBuilder;
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
			List<Stmt> newStmts = new ArrayList<>(edge.getStmts());
			for (Stmt stmt : edge.getStmts()) {
				if (stmt instanceof AssignStmt && !(((AssignStmt<?>) stmt).getVarDecl().getType() instanceof ArrayType)) {
					AssignStmt<?> assignStmt = (AssignStmt<?>) stmt;
					CComplexType leftType = CComplexType.getType(((AssignStmt<?>) stmt).getVarDecl().getRef());
					checkNotNull(leftType);
					Expr<?> expr = assignStmt.getExpr();

					Expr<?> truncatedExpr = leftType.castTo(expr);
					FrontendMetadata.create(truncatedExpr, "cType", leftType);
					if (!expr.equals(truncatedExpr)) {
						atLeastOneAssignmentTruncated = true;
						newStmts.remove(stmt);
						AssignStmt<?> newStmt = Assign(cast(assignStmt.getVarDecl(), assignStmt.getVarDecl().getType()), cast(truncatedExpr, assignStmt.getVarDecl().getType()));
						newStmts.add(newStmt);
					}
				}
			}
			if (atLeastOneAssignmentTruncated) {
				XcfaEdge newEdge = new XcfaEdge(edge.getSource(), edge.getTarget(), newStmts);
				FrontendMetadata.lookupMetadata(edge).forEach((s, o) -> {
					FrontendMetadata.create(newEdge, s, o);
				});
				procBuilder.removeEdge(edge);
				procBuilder.addEdge(newEdge);
			}
		}


	}

	private void splitAndInlineEdges(XcfaProcess.Builder oldBuilder, XcfaProcedure.Builder procBuilder, Map<XcfaEdge, List<XcfaCallStmt>> splittingPoints) {
		splittingPoints.forEach((xcfaEdge, xcfaCallStmts) -> {
			procBuilder.removeEdge(xcfaEdge);
			XcfaCallStmt xcfaCallStmt = xcfaCallStmts.get(0);
			int i = xcfaEdge.getStmts().indexOf(xcfaCallStmt);
			XcfaLocation start = xcfaEdge.getSource();
			XcfaLocation end = xcfaEdge.getTarget();
			if(i > 0) {
				XcfaLocation loc1 = new XcfaLocation("inline" + counter++, Map.of());
				FrontendMetadata.lookupMetadata(xcfaEdge).forEach((s, o) -> {
					FrontendMetadata.create(loc1, s, o);
				});
				procBuilder.addLoc(loc1);
				XcfaEdge edge = new XcfaEdge(start, loc1, sublist(xcfaEdge.getStmts(), 0, i));
				procBuilder.addEdge(edge);
				FrontendMetadata.lookupMetadata(xcfaEdge).forEach((s, o) -> {
					FrontendMetadata.create(edge, s, o);
				});
				start = loc1;
			}
			if(i < xcfaEdge.getStmts().size() - 1) {
				XcfaLocation loc1 = new XcfaLocation("inline" + counter++, Map.of());
				FrontendMetadata.lookupMetadata(xcfaEdge).forEach((s, o) -> {
					FrontendMetadata.create(loc1, s, o);
				});
				procBuilder.addLoc(loc1);
				XcfaEdge edge = new XcfaEdge(loc1, end, sublist(xcfaEdge.getStmts(), i + 1, xcfaEdge.getStmts().size()));
				procBuilder.addEdge(edge);
				FrontendMetadata.lookupMetadata(xcfaEdge).forEach((s, o) -> {
					FrontendMetadata.create(edge, s, o);
				});
				end = loc1;
			}
			Optional<XcfaProcedure> procedureOpt = oldBuilder.getProcedures().stream().filter(xcfaProcedure -> xcfaProcedure.getName().equals(xcfaCallStmt.getProcedure())).findAny();
			checkState(procedureOpt.isPresent());
			XcfaProcedure procedure = new XcfaProcedure(procedureOpt.get());
			for (VarDecl<?> localVar : procedure.getLocalVars()) {
				procBuilder.createVar(localVar, null);
			}
			procedure.getParams().forEach((varDecl, direction) -> procBuilder.createVar(varDecl, null));
			Map<XcfaLocation, XcfaLocation> locationLut = new LinkedHashMap<>();
			procedure.getLocs().forEach(loc -> {
				XcfaLocation copy = XcfaLocation.copyOf(loc);
				locationLut.put(loc, copy);
				procBuilder.addLoc(copy);
			});
			procedure.getEdges().forEach(e -> procBuilder.addEdge(new XcfaEdge(locationLut.get(e.getSource()), locationLut.get(e.getTarget()), e.getStmts())));
			procedure.getFinalLoc().setEndLoc(false);

			int paramCnt = 0;
			List<Stmt> retStmts = new ArrayList<>();
			List<Stmt> initStmts = new ArrayList<>();
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
					initStmts.add(assignStmt);
				}
				if (direction != XcfaProcedure.Direction.IN) {
					Expr<?> expr = xcfaCallStmt.getParams().get(paramCnt);
					checkState(expr instanceof RefExpr && ((RefExpr<?>) expr).getDecl() instanceof VarDecl<?>);
					retStmts.add(Assign(cast((VarDecl<?>) ((RefExpr<?>) expr).getDecl(), varDecl.getType()), cast(varDecl.getRef(), varDecl.getType())));
				}
				++paramCnt;
			}
			XcfaEdge xcfaEdge1 = new XcfaEdge(start, locationLut.get(procedure.getInitLoc()), initStmts);
			FrontendMetadata.lookupMetadata(xcfaEdge).forEach((s, o) -> {
				FrontendMetadata.create(xcfaEdge1, s, o);
			});
			XcfaEdge xcfaEdge2 = new XcfaEdge(locationLut.get(procedure.getFinalLoc()), end, retStmts);
			FrontendMetadata.lookupMetadata(xcfaEdge).forEach((s, o) -> {
				FrontendMetadata.create(xcfaEdge2, s, o);
			});
			procBuilder.addEdge(xcfaEdge1);
			procBuilder.addEdge(xcfaEdge2);
		});
	}

	private List<Stmt> sublist(List<Stmt> stmts, int from, int to) {
		List<Stmt> ret = new ArrayList<>();
		for (int i = 0; i < stmts.size(); i++) {
			if(i >= from && i < to) ret.add(stmts.get(i));
		}
		return ret;
	}


	private boolean handleCallStmts(XcfaProcess.Builder builder, XcfaProcedure mainProcedure, XcfaProcedure.Builder mainProcBuilder, Map<XcfaEdge, List<XcfaCallStmt>> splittingPoints) {
		boolean anyMatch = false;
		for (XcfaEdge edge : mainProcBuilder.getEdges()) {
			boolean stillExists = true;
			while(stillExists) {
				Optional<Stmt> callStmtOpt = edge.getStmts().stream().filter(stmt ->
						stmt instanceof XcfaCallStmt &&
						!alreadyHandled.contains(Tuple2.of(stmt, edge)) &&
						!nopFuncs.contains(((XcfaCallStmt)stmt).getProcedure()) &&
						shouldInlineCall(builder, (XcfaCallStmt) stmt)).findAny();
				if(callStmtOpt.isPresent() ) {
					alreadyHandled.add(Tuple2.of(callStmtOpt.get(), edge));
					anyMatch = true;
					Optional<XcfaProcedure> procedure = builder.getProcedures().stream().filter(xcfaProcedure -> xcfaProcedure.getName().equals(((XcfaCallStmt) callStmtOpt.get()).getProcedure())).findAny();
					if (procedure.isPresent()) {
						splittingPoints.putIfAbsent(edge, new ArrayList<>());
						splittingPoints.get(edge).add((XcfaCallStmt) callStmtOpt.get());
					}
				} else {
					stillExists = false;
				}
			}
		}
		return anyMatch;
	}

	private boolean shouldInlineCall(XcfaProcess.Builder builder, XcfaCallStmt callStmt) {
		Optional<XcfaProcedure> procedure = builder.getProcedures().stream().filter(xcfaProcedure -> xcfaProcedure.getName().equals(callStmt.getProcedure())).findAny();
		if(procedure.isPresent()) {
			Optional<Object> shouldInlineProc = FrontendMetadata.getMetadataValue(procedure.get(), "shouldInline");
			if(shouldInlineProc.isPresent() && shouldInlineProc.get() instanceof Boolean) {
				return (Boolean) shouldInlineProc.get();
			}
			Optional<Object> sourceStatement = FrontendMetadata.getMetadataValue(procedure.get(), "sourceStatement");
			if(sourceStatement.isPresent()) {
				Optional<Object> shouldInline = FrontendMetadata.getMetadataValue(sourceStatement.get(), "shouldInline");
				return shouldInline.isEmpty() || !(shouldInline.get() instanceof Boolean) || (Boolean) shouldInline.get();
			}
		}
		return true;
	}
}
