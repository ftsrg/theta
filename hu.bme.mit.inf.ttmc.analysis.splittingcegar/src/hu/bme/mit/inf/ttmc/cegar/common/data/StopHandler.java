package hu.bme.mit.inf.ttmc.cegar.common.data;

public class StopHandler {
	private volatile boolean isStopped;

	public StopHandler() {
		isStopped = false;
	}

	public void stop() {
		isStopped = true;
	}

	public boolean isStopped() {
		return isStopped;
	}

	public void reset() {
		isStopped = false;
	}
}
