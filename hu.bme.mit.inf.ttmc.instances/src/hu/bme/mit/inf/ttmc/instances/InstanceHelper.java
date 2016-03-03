package hu.bme.mit.inf.ttmc.instances;

import java.io.File;
import java.io.IOException;
import java.net.URL;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Path;
import org.osgi.framework.Bundle;
import org.osgi.framework.FrameworkUtil;

public class InstanceHelper {
	
	public static String getPath(final String fileName) throws IOException {
//		final Bundle bundle = Platform.getBundle("hu.bme.mit.inf.ttmc.instances");
		final Bundle bundle = FrameworkUtil.getBundle(InstanceHelper.class);
		final Path path = new Path(fileName);
		final URL url = FileLocator.find(bundle, path, null);
		final URL fileUrl = FileLocator.toFileURL(url);
		final File file = new File(fileUrl.getPath());
		final String filePath = file.getAbsolutePath();
		return filePath;
	}
	
}
