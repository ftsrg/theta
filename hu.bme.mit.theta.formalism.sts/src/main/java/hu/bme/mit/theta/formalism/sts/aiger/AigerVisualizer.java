package hu.bme.mit.theta.formalism.sts.aiger;

import static com.google.common.base.Preconditions.checkNotNull;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;

/**
 * Utility class for visualizing AIGER files.
 */
public class AigerVisualizer {

	private AigerVisualizer() {
	}

	private static final String INPUTSHAPE = "invhouse";
	private static final String LATCHSHAPE = "rectangle";
	private static final String OUTPUTSHAPE = "invhouse";
	private static final String ANDSHAPE = "ellipse";
	private static final String INVHEAD = "odot";

	/**
	 * Parse and visualize an AIGER file into dot format.
	 *
	 * @param aigerFilePath Path of the input AIGER file
	 * @param outFilePath Path of the output dot file
	 * @throws IOException
	 */
	public static void visualize(final String aigerFilePath, final String outFilePath) throws IOException {
		final BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(aigerFilePath)));
		final PrintWriter pw = new PrintWriter(outFilePath);

		try {
			int inputs, latches, outputs, andGates;
			// Parse header
			final String[] header = checkNotNull(br.readLine(), "Header expected").split(" ");
			inputs = Integer.parseInt(header[2]);
			latches = Integer.parseInt(header[3]);
			outputs = Integer.parseInt(header[4]);
			andGates = Integer.parseInt(header[5]);

			pw.write("digraph \"circuit\" {\n");

			// Inputs
			for (int i = 0; i < inputs; ++i) {
				final int v = Integer.parseInt(br.readLine());
				pw.write("v" + v / 2 + "[label=\"I" + (i + 1) + "\", shape=\"" + INPUTSHAPE
						+ "\", margin=\"0\", width=\"0\", height=\"0\"];\n");
			}

			// Latches
			for (int i = 0; i < latches; ++i) {
				final String v[] = checkNotNull(br.readLine(), "Latch expected").split(" ");
				final int v1 = Integer.parseInt(v[0]);
				final int v2 = Integer.parseInt(v[1]);
				pw.write("v" + v1 / 2 + "[label=\"L" + (i + 1) + "\", shape=\"" + LATCHSHAPE
						+ "\", margin=\"0.05\", width=\"0\", height=\"0\"];\n");
				pw.write("v" + v2 / 2 + ":s -> v" + v1 / 2 + ":n");
				if (v2 % 2 != 0)
					pw.write(" [arrowhead=\"" + INVHEAD + "\"]");
				pw.write(";\n");
			}

			// Outputs
			for (int i = 0; i < outputs; ++i) {
				final int v = Integer.parseInt(br.readLine());
				pw.write("o" + i + "[label=\"O" + (i + 1) + "\", shape=\"" + OUTPUTSHAPE
						+ "\", margin=\"0\", width=\"0\", height=\"0\"];\n");
				pw.write("v" + v / 2 + ":s -> o" + i + ":n");
				if (v % 2 != 0)
					pw.write(" [arrowhead=\"" + INVHEAD + "\"]");
				pw.write(";\n");
			}

			// And gates
			for (int i = 0; i < andGates; ++i) {
				final String[] v = checkNotNull(br.readLine(), "And gate expected").split(" ");
				final int vo = Integer.parseInt(v[0]);
				final int vi1 = Integer.parseInt(v[1]);
				final int vi2 = Integer.parseInt(v[2]);
				pw.write("v" + vo / 2 + "[label=\"A" + (i + 1) + "\", shape=\"" + ANDSHAPE
						+ "\", margin=\"0.02\", width=\"0\", height=\"0\"];\n");
				pw.write("v" + vi1 / 2 + ":s -> v" + vo / 2 + ":nw");
				if (vi1 % 2 != 0)
					pw.write(" [arrowhead=\"" + INVHEAD + "\"]");
				pw.write("\n");
				pw.write("v" + vi2 / 2 + ":s -> v" + vo / 2 + ":ne");
				if (vi2 % 2 != 0)
					pw.write(" [arrowhead=\"" + INVHEAD + "\"]");
				pw.write(";\n");
			}

			pw.print("}");
		} finally {
			pw.close();
			br.close();
		}
	}
}
