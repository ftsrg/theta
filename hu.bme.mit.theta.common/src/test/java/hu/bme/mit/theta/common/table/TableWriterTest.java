package hu.bme.mit.theta.common.table;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;

import org.junit.Assert;
import org.junit.Test;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.table.impl.SimpleTableWriter;

public class TableWriterTest {
	@Test
	public void test() {
		final ByteArrayOutputStream baos = new ByteArrayOutputStream();
		final PrintStream ps = new PrintStream(baos);
		final TableWriter tw = new SimpleTableWriter(ps, ",");

		tw.cell(11).cell(12).newRow();
		tw.cell(2, 2).newRow();
		tw.cell(31).newRow(32);
		tw.cells(ImmutableList.of(41, 42)).newRow();

		final String actual = new String(baos.toByteArray(), StandardCharsets.UTF_8);

		final String nl = System.lineSeparator();
		final String expected = "11,12" + nl + "2," + nl + "31,32" + nl + "41,42" + nl;

		Assert.assertEquals(expected, actual);
	}
}
