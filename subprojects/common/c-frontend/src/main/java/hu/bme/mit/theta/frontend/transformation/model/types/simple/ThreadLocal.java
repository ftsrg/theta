package hu.bme.mit.theta.frontend.transformation.model.types.simple;

public class ThreadLocal extends CSimpleType {
	public static ThreadLocal instance = new ThreadLocal();
	private ThreadLocal(){}

	@Override
	protected void patch(CSimpleType cSimpleType) {
		cSimpleType.setThreadLocal(true);
	}
}
