package hu.bme.mit.theta.xcfa.algorithmselection;

import java.lang.management.GarbageCollectorMXBean;
import java.lang.management.ManagementFactory;

public final class GcTimer {
	public static long getGcTime() {
		long garbageCollectionTime = 0;

		for(GarbageCollectorMXBean gc :	ManagementFactory.getGarbageCollectorMXBeans()) {

			long time = gc.getCollectionTime();

			if(time >= 0) {
				garbageCollectionTime += time;
			}
		}

		return garbageCollectionTime;
	}

	private GcTimer() {};
}
