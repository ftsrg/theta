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
	private Loc errorLoc;
	private Queue<Job> jobs;
	
	private Xcfa2Cfa(XCFA xcfa) {
		this.xcfa = xcfa;
	}
	
	/**
	 * Information required for creating a procedure.
	 * @author laszlo.radnai
	 *
	 */
	private static class Job {
		public final String locPrefix;
		public final Procedure procedure;
		public final Loc initLoc;
		public final Loc finalLoc;
		public final List<VarDecl<?>> passedParams;
		public final VarDecl<?> resultVar;
		public Job(String prefix, Procedure proc, Loc i, Loc f, List<VarDecl<?>> params, VarDecl<?> resVar) {
			locPrefix = prefix;
			procedure = proc;
			initLoc = i;
			finalLoc = f;
			passedParams = params;
			resultVar = resVar;
		}
	}
	
	private void buildProcedure(CFA.Builder builder, Job j) {
		Map<VarDecl<?>, VarDecl<?>> varMapping = new HashMap<>();
		// create new instances of local variables
		for (var vari : j.procedure.getVars()) {
			// use prefix to avoid collisions
			varMapping.put(vari, Decls.Var(j.locPrefix + "_" + vari, vari.getType()));
		}
		Map<VarDecl<?>, VarDecl<?>> paramMapping = new HashMap<>();
		// reuse passed parameters
		for (var i = 0; i < j.passedParams.size(); i++) {
			var oldVar = j.procedure.getParams().get(i);
			var newVar = Decls.Var(j.locPrefix + "_" + oldVar, oldVar.getType());
			paramMapping.put(j.passedParams.get(i), newVar);
			varMapping.put(oldVar, newVar);
		}
		// XCFA.Loc to Loc 
		Map<Location, Loc> mapping = new HashMap<>();
		for (Location xcfaLoc : j.procedure.getLocs()) {
			Loc loc;
			if (xcfaLoc == j.procedure.getErrorLoc()) {
				loc = errorLoc;
			} else {
				loc = builder.createLoc(j.locPrefix + xcfaLoc.getName());
			}
			mapping.put(xcfaLoc, loc);
		}
		builder.createEdge(j.initLoc, mapping.get(j.procedure.getInitLoc()), Stmts.Skip());
		builder.createEdge(mapping.get(j.procedure.getFinalLoc()), j.finalLoc, Stmts.Skip());
		// avoid naming collisions
		int callCtr = 0;
		
		for (Edge e: j.procedure.getEdges()) {
			var src = mapping.get(e.getSource());
			var trg = mapping.get(e.getTarget());
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
					jobs.add(new Job(j.locPrefix + "_" + callCtr + proc.getName(), proc, src, trg, params, res));
					callCtr++;
				} else {
					Stmt applied = stmts.get(0).accept(VarMapperStmtVisitor.getInstance(), varMapping);
					builder.createEdge(src, trg, stmts.get(0));
				}
			}
		}
	}
	
	private CFA transform() {
		// CFA can only contain: Havoc, Assign, Assume and Skip
		CFA.Builder builder = CFA.builder();
		var initLoc = builder.createLoc("IL");
		var finalLoc = builder.createLoc("FL");
		errorLoc = builder.createLoc("EL");
		builder.setInitLoc(initLoc);
		builder.setErrorLoc(errorLoc);
		builder.setFinalLoc(finalLoc);
		jobs = new ArrayDeque<>();
		jobs.add(new Job("", xcfa.getMainProcess().getMainProcedure(), initLoc, finalLoc, List.of(), null));
		while (!jobs.isEmpty()) {
			buildProcedure(builder, jobs.poll());
		}
		
		return builder.build();
	}
	
	public static CFA toCfa(XCFA xcfa) {
		Preconditions.checkArgument(xcfa.getProcesses().size() == 1);
		var transformer = new Xcfa2Cfa(xcfa);
		return transformer.transform();
	}
}
