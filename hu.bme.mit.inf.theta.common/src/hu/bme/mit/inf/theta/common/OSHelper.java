package hu.bme.mit.inf.theta.common;

import com.google.common.base.StandardSystemProperty;

public class OSHelper {

	private OSHelper() {

	}

	public enum OperatingSystem {
		WINDOWS, LINUX
	}

	public static OperatingSystem getOS() {

		final String os = StandardSystemProperty.OS_NAME.value();

		if (os.toLowerCase().startsWith("linux"))
			return OperatingSystem.LINUX;
		else if (os.toLowerCase().startsWith("windows"))
			return OperatingSystem.WINDOWS;
		else
			throw new RuntimeException("Operating system \"" + os + "\" not supported.");
	}

	public static void main(final String[] args) {
		System.out.println(getOS());
	}
}
