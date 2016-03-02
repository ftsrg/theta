package hu.bme.mit.inf.ttmc.constraint.ui;

import java.io.File;
import java.io.IOException;
import java.net.URL;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.osgi.framework.Bundle;

public class ConstraintInstanceHelper {
	
	public static String getPath(final String fileName) throws IOException {
		final Bundle bundle = Platform.getBundle("hu.bme.mit.inf.ttmc.models");
		final Path path = new Path("instances/constraint/" + fileName);
		final URL url = FileLocator.find(bundle, path, null);
		final URL fileUrl = FileLocator.toFileURL(url);
		final File file = new File(fileUrl.getPath());
		final String filePath = file.getAbsolutePath();
		return filePath;
	}
	
}
