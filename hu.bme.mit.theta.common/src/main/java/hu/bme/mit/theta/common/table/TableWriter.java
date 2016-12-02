package hu.bme.mit.theta.common.table;

/**
 * Interface for printing tables with cells and rows.
 */
public interface TableWriter {
	default TableWriter cell(final Object obj) {
		return cell(obj, 1);
	}

	default TableWriter cells(final Iterable<?> objs) {
		objs.forEach(this::cell);
		return this;
	}

	TableWriter cell(Object obj, int colspan);

	TableWriter newRow();

	default TableWriter newRow(final Object obj) {
		return cell(obj).newRow();
	}
}
