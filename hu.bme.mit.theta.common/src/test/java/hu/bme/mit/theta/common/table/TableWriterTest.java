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
		final TableWriter tw = new SimpleTableWriter(ps, ",", "X", "Y");

		tw.cell(11).cell(12).newRow();
		tw.cell(2, 2).newRow();
		tw.cell(31).newRow(32);
		tw.cells(ImmutableList.of(41, 42)).newRow();

		final String actual = new String(baos.toByteArray(), StandardCharsets.UTF_8);

		final String nl = System.lineSeparator();
		final String expected = "X11Y,X12Y" + nl + "X2Y," + nl + "X31Y,X32Y" + nl + "X41Y,X42Y" + nl;

		Assert.assertEquals(expected, actual);
	}
}
