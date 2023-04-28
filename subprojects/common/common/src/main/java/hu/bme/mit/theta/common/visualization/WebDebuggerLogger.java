package hu.bme.mit.theta.common.visualization.writer;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.ArrayList;

public class WebDebuggerLogger {
	private static final WebDebuggerLogger instance = new WebDebuggerLogger();

	private final ArrayList<String> iterations = new ArrayList<String>();
	private final ArrayList<String> traces = new ArrayList<String>();
	private String title = "Cfa";

	private WebDebuggerLogger() {
	}


	public static WebDebuggerLogger getInstance() {
		return instance;
	}

	public void addIteration(int iteration, String arg, String prec) {
		StringBuilder sb = new StringBuilder();
		sb.append("{").append(System.lineSeparator()).append("\"iteration\": ").append(iteration).append(",");
		sb.append("\"arg\": ").append(arg).append(",");
		sb.append("\"precision\": \"").append(prec).append("\"");
		sb.append("}");
		iterations.add(sb.toString());
	}

	public void setTitle(String title) {
		this.title = title;
	}

	private String getFileContent() {
		StringBuilder sb = new StringBuilder();
		sb.append("{").append(System.lineSeparator());
		sb.append("\"title\": \"").append(title).append("\",").append(System.lineSeparator());
		sb.append("\"date\": \"").append(java.time.LocalDateTime.now()).append("\",").append(System.lineSeparator());
		sb.append("\"iterations\": [");
		for (String iteration : iterations) {
			sb.append(iteration).append(",");
		}
		sb.deleteCharAt(sb.length() - 1);
		sb.append("],").append(System.lineSeparator());
		sb.append("\"traces\": [");
		for (String trace : traces) {
			sb.append("\"").append(trace).append("\"").append(",\n");
		}
		sb.deleteCharAt(sb.length() - 1);
		sb.append("]").append(System.lineSeparator());
		sb.append("}");
		return sb.toString();
	}

	public void writeToFile(String fileName) {
		String content = getFileContent();

		final File file = new File(fileName);
		try (PrintWriter printWriter = new PrintWriter(file)) {
			printWriter.write(content);
		} catch (final FileNotFoundException e) {
			System.out.println("File not found");
		}
	}

	public void addTrace(String trace) {
		// remove all linebreaks
		trace = trace.replaceAll("[\\r\\n]", "");
		trace = trace.replaceAll("\\s+", " ");
		traces.add(trace);
	}
}
