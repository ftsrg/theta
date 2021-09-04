package hu.bme.mit.theta.analysis.algorithm;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

public class ArgStatisticsWriter {
	public static ArgStatisticsWriter instance = new ArgStatisticsWriter();
	private File argStatisticsFileName = null;

	public void setTaskfileName(String taskPath) {
		argStatisticsFileName = new File(taskPath + ".arg.csv");
	}

	public void writeArgStatistics(long startNodes, long startIncompleteNodes, long endNodes, long endIncompleteNodes) {
		if(argStatisticsFileName!=null) {
			try (BufferedWriter bw = new BufferedWriter(new FileWriter(argStatisticsFileName, true))) {
				bw.append(String.valueOf(startNodes)).append(",");
				bw.append(String.valueOf(startIncompleteNodes)).append(",");
				bw.append(String.valueOf(endNodes)).append(",");
				bw.append(String.valueOf(endIncompleteNodes)).append(System.lineSeparator());
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}
}
