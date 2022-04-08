package hu.bme.mit.theta.common;

import hu.bme.mit.theta.common.version.VersionInfo;

import java.io.PrintStream;

public class CliUtils {
	private CliUtils() { }

	public static void printVersion(PrintStream ps) {
		ps.println(VersionInfo.getInstance().getName() + " " + VersionInfo.getInstance().getVersion());
		ps.println("Branch: " + VersionInfo.getInstance().getGitBranch());
		ps.println("Commit: " + VersionInfo.getInstance().getGitCommit());
	}
}
