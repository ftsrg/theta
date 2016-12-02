package hu.bme.mit.theta.common.table;

public interface TableWriter {
	default TableWriter cell(final Object obj) {
		cell(obj, 1);
		return this;
	}

	default TableWriter cells(final Iterable<?> objs) {
		objs.forEach(this::cell);
		return this;
	}

	TableWriter cell(Object obj, int colspan);

	TableWriter newRow();
}
