package hu.bme.mit.theta.xcfa.analysis.algorithmselection;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

public class CpuTimeKeeper {
	public static long getCurrentCpuTime() {
		long pid = ProcessHandle.current().pid();
		long cputime = 0;
		try {
			// TODO if the child process closing while we are taking measurements (which it WILL do between configs)
			// that would cause false times, so we should definitely think this one through
			Process process = Runtime.getRuntime().exec("ps --pid " + pid + " -o time");
			BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
			String line = "";
			String cputimeString = reader.readLine(); // skip the TIME header
			while((cputimeString = reader.readLine())!=null) {
				System.err.println(cputimeString);
				String[] split = cputimeString.split(":");
				cputime += Long.parseLong(split[0])*3600+Long.parseLong(split[1])*60+Long.parseLong(split[2]);
				System.err.println(cputime);
			}
			System.err.println("");
		} catch (IOException e) {
			e.printStackTrace();
		}
		return cputime;
	}
}
