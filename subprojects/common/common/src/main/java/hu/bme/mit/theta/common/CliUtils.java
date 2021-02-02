package hu.bme.mit.theta.common;

import java.io.PrintStream;

public class CliUtils {
	private CliUtils() { }

	public static void printVersion(PrintStream ps) {
		String ver = new CliUtils().getClass().getPackage().getImplementationVersion();
		if (ver == null) ver = "Unknown version. Are you running from JAR file?";
		ps.println(ver);
	}
}
