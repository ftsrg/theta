package hu.bme.mit.theta.frontend.mdd;

import hu.bme.mit.theta.common.table.TableWriter;

import java.util.Arrays;

public final class ModelProperties {
	private static final String[] headers = new String[]{"id", "Name", "Type", "#Place", "#Transition", "#Arc",
		"HasReadOnlyEffect",
		"HasReadOnlyEffectOnTop"};
	
	private final PtNetSystem model;
	private final String id;
	
	public ModelProperties(final PtNetSystem model, String id) {
		this.model = model;
		this.id = id;
	}
	
	public static void printHeader(TableWriter writer) {
		writer.cells(Arrays.asList(headers));
		writer.newRow();
	}
	
	public void printData(TableWriter writer) {
		writer.cell(id);
		writer.cell(model.getName());
		writer.cell("P/T net");
		writer.cell(model.getPlaceCount());
		writer.cell(model.getTransitionCount());
		writer.cell(model.getArcCount());
		writer.cell(model.hasReadOnlyEffect);
		writer.cell(model.hasReadOnlyEffectOnTop);
		writer.newRow();
	}
}
