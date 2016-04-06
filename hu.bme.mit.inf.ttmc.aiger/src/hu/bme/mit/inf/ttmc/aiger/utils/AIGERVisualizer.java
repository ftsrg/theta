package hu.bme.mit.inf.ttmc.aiger.utils;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;

public class AIGERVisualizer {
	
	private static final String INPUTSHAPE = "invhouse";
	private static final String LATCHSHAPE = "rectangle";
	private static final String OUTPUTSHAPE = "invhouse";
	private static final String ANDSHAPE = "ellipse";
	private static final String INVHEAD = "odot";
	
	public static void visualize(String fileName, String output) throws IOException {
		BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(fileName)));
		PrintWriter pw = new PrintWriter(output);
		
		int inputs, latches, outputs, andGates;
		// Parse header
		String[] header = br.readLine().split(" ");
		inputs = Integer.parseInt(header[2]);
		latches = Integer.parseInt(header[3]);
		outputs = Integer.parseInt(header[4]);
		andGates = Integer.parseInt(header[5]);
		
		pw.write("digraph \"circuit\" {\n");
		
		// Inputs
		for(int i = 0; i < inputs; ++i) {
			int v = Integer.parseInt(br.readLine());
			pw.write("v" + v/2 + "[label=\"I" + (i+1) + "\", shape=\"" + INPUTSHAPE + "\", margin=\"0\", width=\"0\", height=\"0\"];\n");
		}
		
		// Latches
		for (int i = 0; i < latches; ++i) {
			String v[] = br.readLine().split(" ");
			int v1 = Integer.parseInt(v[0]);
			int v2 = Integer.parseInt(v[1]);
			pw.write("v" + v1/2 + "[label=\"L" + (i+1) + "\", shape=\"" + LATCHSHAPE + "\", margin=\"0.05\", width=\"0\", height=\"0\"];\n");
			pw.write("v" + v2/2 + ":s -> v" + v1/2 + ":n");
			if (v2%2 == 1) pw.write(" [arrowhead=\"" + INVHEAD + "\"]");
			pw.write(";\n");
		}
		
		// Outputs
		for (int i = 0; i < outputs; ++i) {
			int v = Integer.parseInt(br.readLine());
			pw.write("o" + i + "[label=\"O" + (i+1) + "\", shape=\"" + OUTPUTSHAPE + "\", margin=\"0\", width=\"0\", height=\"0\"];\n");
			pw.write("v" + v/2 + ":s -> o" + i + ":n");
			if (v%2 == 1) pw.write(" [arrowhead=\"" + INVHEAD + "\"]");
			pw.write(";\n");
		}
		
		// And gates
		for (int i = 0; i < andGates; ++i) {
			String[] v = br.readLine().split(" ");
			int vo = Integer.parseInt(v[0]);
			int vi1 = Integer.parseInt(v[1]);
			int vi2 = Integer.parseInt(v[2]);
			pw.write("v" + vo/2 + "[label=\"A" + (i+1) + "\", shape=\"" + ANDSHAPE + "\", margin=\"0.02\", width=\"0\", height=\"0\"];\n");
			pw.write("v" + vi1/2 + ":s -> v" + vo/2 + ":nw");
			if (vi1%2 == 1) pw.write(" [arrowhead=\"" + INVHEAD + "\"]");
			pw.write("\n");
			pw.write("v" + vi2/2 + ":s -> v" + vo/2 + ":ne");
			if (vi2%2 == 1) pw.write(" [arrowhead=\"" + INVHEAD + "\"]");
			pw.write(";\n");
		}
		
		pw.print("}");
		pw.close();
		br.close();
		
	}
}
