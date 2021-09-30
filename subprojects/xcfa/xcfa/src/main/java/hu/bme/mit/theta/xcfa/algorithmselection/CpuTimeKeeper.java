package hu.bme.mit.theta.xcfa.algorithmselection;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

public class CpuTimeKeeper {
	public static long getCurrentCpuTime() {
		long pid = ProcessHandle.current().pid();
		long cputime = 0;
		try {
			Process process = Runtime.getRuntime().exec("ps --pid " + pid + " -o time");
			BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
			String line = "";
			reader.readLine();
			String cputimeString = reader.readLine();
			String[] split = cputimeString.split(":");
			cputime = Long.parseLong(split[0])*3600+Long.parseLong(split[1])*60+Long.parseLong(split[2]);
		} catch (IOException e) {
			e.printStackTrace();
		}
		return cputime;
	}
}
