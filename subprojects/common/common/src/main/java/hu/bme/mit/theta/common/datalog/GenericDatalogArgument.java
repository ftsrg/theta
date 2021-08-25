package hu.bme.mit.theta.common.datalog;

public class GenericDatalogArgument<T> implements DatalogArgument {
	private final T content;

	private GenericDatalogArgument(T content) {
		this.content = content;
	}

	public static <T> GenericDatalogArgument<T> createArgument(T content) {
		return new GenericDatalogArgument<>(content);
	}

	public T getContent() {
		return content;
	}

	@Override
	public String toString() {
		return content.toString();
	}

	@Override
	public boolean equals(Object o) {
		if (o instanceof GenericDatalogArgument) return content.equals(((GenericDatalogArgument<?>) o).getContent());
		else return content.equals(o);
	}

	@Override
	public int hashCode() {
		return content.hashCode();
	}
}
