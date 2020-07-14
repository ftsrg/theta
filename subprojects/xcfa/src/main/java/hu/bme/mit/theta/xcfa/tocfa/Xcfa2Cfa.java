package hu.bme.mit.theta.xcfa.tocfa;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Queue;

import com.google.common.base.Preconditions;

import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.CFA.Loc;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.Stmts;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.XCFA.Process.Procedure;
import hu.bme.mit.theta.xcfa.XCFA.Process.Procedure.Edge;
import hu.bme.mit.theta.xcfa.XCFA.Process.Procedure.Location;
import hu.bme.mit.theta.xcfa.dsl.CallStmt;
import hu.bme.mit.theta.xcfa.tocfa.utils.VarMapperStmtVisitor;

/**
 * Creates a CFA from XCFA.
 * 
 * Only works for single thread.
 * Does not work support recursion.
 * Inlines functions.
 * TODO check for cycles
 * 
 * TODO invent a way to pass parameters
 * @author laszlo.radnai
 *
 */
public class Xcfa2Cfa {
	private final XCFA xcfa;
	private final Loc errorLoc;
	private final Queue<ProcedureBuildData> procQueue;
	private final CFA.Builder builder;
	
	private Xcfa2Cfa(XCFA xcfa) {
		this.xcfa = xcfa;
		builder = CFA.builder();
		procQueue = new ArrayDeque<>();
		errorLoc = builder.createLoc("EL");
	}
	
	/**
	 * Information required for creating a procedure.
	 * @author laszlo.radnai
	 *
	 */
	private static class ProcedureBuildData {
		public final String locPrefix;
		public final Procedure procedure;
		public final Loc initLoc;
		public final Loc finalLoc;
		public final List<VarDecl<?>> passedParams;
		public final VarDecl<?> resultVar;
		public ProcedureBuildData(String prefix, Procedure proc, Loc i, Loc f, List<VarDecl<?>> params, VarDecl<?> resVar) {
			locPrefix = prefix;
			procedure = proc;
			initLoc = i;
			finalLoc = f;
			passedParams = params;
			resultVar = resVar;
		}
	}
	
	private static class ProcedureBuilder {
		final Map<VarDecl<?>, VarDecl<?>> varMapping = new HashMap<>();
		VarDecl<?> resultVar = null;
		final Map<VarDecl<?>, VarDecl<?>> paramMapping = new HashMap<>();
		final ProcedureBuildData j;
		final Map<Location, Loc> locationMapping = new HashMap<>();
		final CFA.Builder builder;
		final Loc errorLoc;
		final Queue<ProcedureBuildData> procQueue;
		
		private ProcedureBuilder(Xcfa2Cfa parent, ProcedureBuildData j) {
			errorLoc=parent.errorLoc;
			this.j = j;
			this.builder = parent.builder;
			procQueue = parent.procQueue;
		}
		
		void process() {
			collectVars();
			collectParams();
			collectLocations();
			linkInitFinal();
			collectEdges();
		}
		
		private void collectVars() {
			// create new instances of local variables
			for (var vari : j.procedure.getVars()) {
				// use prefix to avoid collisions
				varMapping.put(vari, Decls.Var(j.locPrefix + "_" + vari, vari.getType()));
				if ("result".equals(vari.getName())) {
					resultVar = vari;
				}
			}
		}
		
		private void collectParams() {
			// parameters are copied by value
			// TODO pass by reference could be achieved, but we cannot express it in XCFA
			for (var i = 0; i < j.passedParams.size(); i++) {
				var oldVar = j.procedure.getParams().get(i);
				var newVar = Decls.Var(j.locPrefix + "_" + oldVar, oldVar.getType());
				paramMapping.put(j.passedParams.get(i), newVar);
				varMapping.put(oldVar, newVar);
			}
		}
		
		private void collectLocations() {
			// XCFA.Loc to Loc 
			for (Location xcfaLoc : j.procedure.getLocs()) {
				Loc loc;
				if (xcfaLoc == j.procedure.getErrorLoc()) {
					loc = errorLoc;
				} else {
					loc = builder.createLoc(j.locPrefix + xcfaLoc.getName());
				}
				locationMapping.put(xcfaLoc, loc);
			}
		}
		
		private void linkInitFinal() {
			builder.createEdge(j.initLoc, locationMapping.get(j.procedure.getInitLoc()), Stmts.Skip()); // TODO here params must be initialized (instead of skip)
			builder.createEdge(locationMapping.get(j.procedure.getFinalLoc()), j.finalLoc, Stmts.Skip()); // TODO here result (if present) must be set (instead of skip)
		}
		
		private void collectEdges() {
			int callCtr = 0;
			for (Edge e: j.procedure.getEdges()) {
				var src = locationMapping.get(e.getSource());
				var trg = locationMapping.get(e.getTarget());
				var stmts = e.getStmts();
				Preconditions.checkState(stmts.size() <= 1, "XCFA must contain at most 1 stmt");
				if (stmts.isEmpty()) {
					builder.createEdge(src, trg, Stmts.Skip());
				} else {
					var stmt = stmts.get(0);
					if (stmt instanceof CallStmt) {
						var proc = ((CallStmt) stmt).getProcedure();
						var params = ((CallStmt) stmt).getParams();
						var res = ((CallStmt) stmt).getVar();
						procQueue.add(new ProcedureBuildData(j.locPrefix + "_" + callCtr + proc.getName(), proc, src, trg, params, res));
						callCtr++;
					} else {
						Stmt applied = stmts.get(0).accept(VarMapperStmtVisitor.getInstance(), varMapping);
						builder.createEdge(src, trg, stmts.get(0));
					}
				}
			}
		}
		
		public static void process(Xcfa2Cfa parent, ProcedureBuildData p) {
			new ProcedureBuilder(parent, p).process();
		}
	}
	
	private CFA transform() {
		// CFA can only contain: Havoc, Assign, Assume and Skip
		var initLoc = builder.createLoc("IL");
		var finalLoc = builder.createLoc("FL");
		builder.setInitLoc(initLoc);
		builder.setErrorLoc(errorLoc);
		builder.setFinalLoc(finalLoc);
		procQueue.add(new ProcedureBuildData("", xcfa.getMainProcess().getMainProcedure(), initLoc, finalLoc, List.of(), null));
		while (!procQueue.isEmpty()) {
			ProcedureBuilder.process(this, procQueue.poll());
		}
		
		return builder.build();
	}
	
	public static CFA toCfa(XCFA xcfa) {
		Preconditions.checkArgument(xcfa.getProcesses().size() == 1);
		var transformer = new Xcfa2Cfa(xcfa);
		return transformer.transform();
	}
}
