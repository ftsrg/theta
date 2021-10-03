package hu.bme.mit.theta.xcfa.analysis.algorithmselection;

import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.frontend.transformation.CStmtCounter;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.utils.XcfaUtils;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

/**
 * Class that extracts statistical information out of the input C program and the (X)CFA
 * and is capable of csv (one line, that can be merged with other similar csvs) and txt (human readable) output
 */
public class ModelStatistics {
	private String modelName;
	private int varCount;
	private long havocCount;
	private int locCount;
	private int edgeCount;
	private long skipEdgeCount;
	private long assumeCount;
	private long assignCount;
	private int cyclomaticComplexity;
	private int forLoops;
	private int whileLoops;
	private int branches;

	private ModelStatistics() {}

	// currently not used, but could be useful later
	public static ModelStatistics createCfaStatistics(CFA cfa, String modelName) {
		ModelStatistics ret = new ModelStatistics();
		ret.modelName = modelName;
		ret.varCount = cfa.getVars().size();
		ret.havocCount = cfa.getEdges().stream().filter(edge -> edge.getStmt() instanceof HavocStmt).count();
		ret.locCount = cfa.getLocs().size();
		ret.edgeCount = cfa.getEdges().size();
		ret.skipEdgeCount = cfa.getEdges().stream().
				filter(edge -> edge.getStmt().equals(SkipStmt.getInstance())).count();
		ret.assumeCount = cfa.getEdges().stream().filter(edge -> edge.getStmt() instanceof AssumeStmt).count();
		ret.assignCount = cfa.getEdges().stream().filter(edge -> edge.getStmt() instanceof AssignStmt).count();

		ret.cyclomaticComplexity = cfa.getEdges().size() - cfa.getLocs().size() + 2;

		ret.forLoops = CStmtCounter.getForLoops();
		ret.whileLoops = CStmtCounter.getWhileLoops();
		ret.branches = CStmtCounter.getWhileLoops();

		return ret;
	}

	public static ModelStatistics createXcfaStatistics(final XCFA xcfa, final String modelName) {
		ModelStatistics ret = new ModelStatistics();
		ret.modelName = modelName;
		ret.varCount = XcfaUtils.getVars(xcfa).size();
		ret.havocCount = xcfa.getProcesses().stream().map(
				proc -> proc.getProcedures().stream().map(
						p -> p.getEdges().stream().map(
								e -> e.getLabels().stream().filter(edge -> edge instanceof XcfaLabel.StmtXcfaLabel &&  edge.getStmt() instanceof HavocStmt).count()
						).reduce(Long::sum).orElse(0L)
				).reduce(Long::sum).orElse(0L)).reduce(Long::sum).orElse(0L);
		ret.locCount = xcfa.getProcesses().stream().map(proc -> proc.getProcedures().stream().map(p -> p.getLocs().size()).reduce(Integer::sum).orElse(0)).reduce(Integer::sum).orElse(0);
		ret.edgeCount = xcfa.getProcesses().stream().map(proc -> proc.getProcedures().stream().map(p -> p.getEdges().size()).reduce(Integer::sum).orElse(0)).reduce(Integer::sum).orElse(0);
		ret.skipEdgeCount = xcfa.getProcesses().stream().map(
				proc -> proc.getProcedures().stream().map(
						p -> p.getEdges().stream().map(
								e -> e.getLabels().stream().filter(edge -> edge instanceof XcfaLabel.StmtXcfaLabel &&  edge.getStmt() instanceof SkipStmt).count()
						).reduce(Long::sum).orElse(0L)
				).reduce(Long::sum).orElse(0L)).reduce(Long::sum).orElse(0L);
		ret.assumeCount = xcfa.getProcesses().stream().map(
				proc -> proc.getProcedures().stream().map(
						p -> p.getEdges().stream().map(
								e -> e.getLabels().stream().filter(edge -> edge instanceof XcfaLabel.StmtXcfaLabel &&  edge.getStmt() instanceof AssumeStmt).count()
						).reduce(Long::sum).orElse(0L)
				).reduce(Long::sum).orElse(0L)).reduce(Long::sum).orElse(0L);
		ret.assignCount = xcfa.getProcesses().stream().map(
				proc -> proc.getProcedures().stream().map(
						p -> p.getEdges().stream().map(
								e -> e.getLabels().stream().filter(edge -> edge instanceof XcfaLabel.StmtXcfaLabel &&  edge.getStmt() instanceof AssignStmt).count()
						).reduce(Long::sum).orElse(0L)
				).reduce(Long::sum).orElse(0L)).reduce(Long::sum).orElse(0L);

		ret.cyclomaticComplexity = ret.edgeCount - ret.locCount + 2;

		ret.forLoops = CStmtCounter.getForLoops();
		ret.whileLoops = CStmtCounter.getWhileLoops();
		ret.branches = CStmtCounter.getWhileLoops();
		return ret;
	}

	public void writeToCsv(File file) {
		StringBuilder stringBuilder = new StringBuilder();
		stringBuilder.append(modelName).append("\t");
		stringBuilder.append(varCount).append("\t");
		stringBuilder.append(havocCount).append("\t");
		stringBuilder.append(locCount).append("\t");
		stringBuilder.append(edgeCount).append("\t");
		stringBuilder.append(skipEdgeCount).append("\t");
		stringBuilder.append(assumeCount).append("\t");
		stringBuilder.append(assignCount).append("\t");
		stringBuilder.append(cyclomaticComplexity).append("\t");
		stringBuilder.append(forLoops).append("\t");
		stringBuilder.append(whileLoops).append("\t");
		stringBuilder.append(branches).append("\t");

		try (BufferedWriter bw = new BufferedWriter(new FileWriter(file))) {
			bw.write(stringBuilder.toString());
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public void writeToTxt(File file) {
		StringBuilder stringBuilder = new StringBuilder();
		stringBuilder.append("XCFA-data varCount ").append(locCount).append(System.lineSeparator());
		stringBuilder.append("XCFA-data havocCount ").append(havocCount).append(System.lineSeparator());
		stringBuilder.append("XCFA-data locCount ").append(locCount).append(System.lineSeparator());
		stringBuilder.append("XCFA-data edgeCount ").append(edgeCount).append(System.lineSeparator());
		stringBuilder.append("XCFA-data skipEdgeCount ").append(skipEdgeCount).append(System.lineSeparator());
		stringBuilder.append("XCFA-data assumeStmts ").append(assumeCount).append("\n"); // assumes
		stringBuilder.append("XCFA-data assignStmts ").append(assignCount).append("\n"); // assign
		stringBuilder.append("XCFA-data cyclomatic complexity ").append(cyclomaticComplexity).append(System.lineSeparator());

		stringBuilder.append("C-data forLoops ").append(forLoops).append("\n"); // for loops
		stringBuilder.append("C-data whileLoops ").append(whileLoops).append("\n"); // while loops
		stringBuilder.append("C-data branches ").append(branches).append("\n"); // branches

		try (BufferedWriter bw = new BufferedWriter(new FileWriter(file))) {
			bw.write(stringBuilder.toString());
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public int getBranches() {
		return branches;
	}

	public int getCyclomaticComplexity() {
		return cyclomaticComplexity;
	}

	public int getEdgeCount() {
		return edgeCount;
	}

	public int getForLoops() {
		return forLoops;
	}

	public int getLocCount() {
		return locCount;
	}

	public int getVarCount() {
		return varCount;
	}

	public int getWhileLoops() {
		return whileLoops;
	}

	public long getAssignCount() {
		return assignCount;
	}

	public long getAssumeCount() {
		return assumeCount;
	}

	public long getHavocCount() {
		return havocCount;
	}

	public long getSkipEdgeCount() {
		return skipEdgeCount;
	}

	public String getModelName() {
		return modelName;
	}
}
