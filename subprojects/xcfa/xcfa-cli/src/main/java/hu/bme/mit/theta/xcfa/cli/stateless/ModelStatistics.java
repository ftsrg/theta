package hu.bme.mit.theta.xcfa.cli.stateless;

import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;
import hu.bme.mit.theta.frontend.transformation.CStmtCounter;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.List;
import java.util.stream.Collectors;

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

	private ModelStatistics() {
	}

	static ModelStatistics createCfaStatistics(CFA cfa, String modelName) {
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

	void writeToCsv(File file) {
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

	void writeToTxt(File file) {
		StringBuilder stringBuilder = new StringBuilder();
		stringBuilder.append("CFA-data varCount ").append(locCount).append(System.lineSeparator());
		stringBuilder.append("CFA-data havocCount ").append(havocCount).append(System.lineSeparator());
		stringBuilder.append("CFA-data locCount ").append(locCount).append(System.lineSeparator());
		stringBuilder.append("CFA-data edgeCount ").append(edgeCount).append(System.lineSeparator());
		stringBuilder.append("CFA-data skipEdgeCount ").append(skipEdgeCount).append(System.lineSeparator());
		stringBuilder.append("CFA-data assumeStmts ").append(assumeCount).append("\n"); // assumes
		stringBuilder.append("CFA-data assignStmts ").append(assignCount).append("\n"); // assign
		stringBuilder.append("CFA-data cyclomatic complexity ").append(cyclomaticComplexity).append(System.lineSeparator());

		stringBuilder.append("C-data forLoops ").append(CStmtCounter.getForLoops()).append("\n"); // for loops
		stringBuilder.append("C-data whileLoops ").append(CStmtCounter.getWhileLoops()).append("\n"); // while loops
		stringBuilder.append("C-data branches ").append(CStmtCounter.getBranches()).append("\n"); // branches

		try (BufferedWriter bw = new BufferedWriter(new FileWriter(file))) {
			bw.write(stringBuilder.toString());
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}
