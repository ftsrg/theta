package hu.bme.mit.theta.xcfa.analysis.algorithmselection;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

public class CpuTimeKeeper {
	static long closedSolverTimes = 0;

	/**
	 * Temporary solution:
	 * We cannot measure the time spent in child processes that are closed already,
	 * so this function has to be called before closing the solvers (with SolverManager.closeAll())
	 * and it saves the cpu time of these processes, before they are closed and
	 * adds it to the cpu time measured in getCurrentCpuTime()
	 */
	public static void saveSolverTimes() {
		long pid = ProcessHandle.current().pid();
		long solvertimes = 0;
		try {
			Process process = Runtime.getRuntime().exec("ps --ppid " + pid + " -o time");
			BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
			String line = "";
			String cputimeString = reader.readLine(); // skip the TIME header
			while((cputimeString = reader.readLine())!=null) {
				String[] split = cputimeString.split(":");
				solvertimes += Long.parseLong(split[0])*3600+Long.parseLong(split[1])*60+Long.parseLong(split[2]);
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
		closedSolverTimes+=solvertimes;
	}

	/**
	 * Measures the time spent in this process and child processes (solver processes)
	 */
	public static long getCurrentCpuTime() {
		long pid = ProcessHandle.current().pid();
		long cputime = closedSolverTimes;
		try {
			Process process = Runtime.getRuntime().exec("ps --pid " + pid + " --ppid " + pid + " -o time");
			BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
			String line = "";
			String cputimeString = reader.readLine(); // skip the TIME header
			while((cputimeString = reader.readLine())!=null) {
				String[] split = cputimeString.split(":");
				cputime += Long.parseLong(split[0])*3600+Long.parseLong(split[1])*60+Long.parseLong(split[2]);
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
		return cputime;
	}
}
