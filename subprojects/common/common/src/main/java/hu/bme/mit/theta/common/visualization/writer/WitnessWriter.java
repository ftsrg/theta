package hu.bme.mit.theta.common.visualization.writer;

import hu.bme.mit.theta.common.visualization.Alignment;
import hu.bme.mit.theta.common.visualization.CompositeNode;
import hu.bme.mit.theta.common.visualization.Edge;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.Node;
import jdk.jshell.spi.ExecutionControl;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.security.DigestInputStream;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.time.LocalDateTime;

/**
 * Class for writing graphs in the SV-Comp witness format.
 * Limitations:
 * - All node attributes, except labels are ignored.
 * - Composite nodes are ignored (handled the same as simple nodes.
 * - All edge attributes, except labels are ignored.
 */
public class WitnessWriter extends AbstractGraphWriter {
	private String programHash;
	private boolean isViolationWitness;
	private String toolName = "theta"; // TODO maybe we should add the version number to this field as well
	private String sourceCodeLang = "C";
	private String architecture = "32bit"; // TODO add 64bit option later
	private LocalDateTime creationTime;
	private String specification;


	public static WitnessWriter createViolationWitnessWriter(String programFile, String specification) {
		WitnessWriter ww = new WitnessWriter(programFile, specification, true);
		return ww;
	}

	public static WitnessWriter createCorrectnessWitnessWriter(String programFile, String specification) {
		WitnessWriter ww = new WitnessWriter(programFile, specification, false);

		return ww;
	}

	private WitnessWriter(String programFile, String specification, boolean isViolationWitness) {
		programHash = createTaskHash(programFile);
		this.isViolationWitness = isViolationWitness;
		this.specification = specification;
		this.creationTime = LocalDateTime.now();
	}

	@Override
	public String writeString(Graph graph) {
		final StringBuilder sb = new StringBuilder();
		printKeys(sb);
		sb.append("<graph edgedefault=\"directed\">").append(System.lineSeparator());

		graph.getRootNodes().forEach(n -> printNode(n, sb));

		for (final Node node : graph.getNodes()) {
			printEdges(node, sb);
		}

		sb.append(" </graph>");
		sb.append(System.lineSeparator());
		sb.append("</graphml>");
		return sb.toString();
	}

	private void printKeys(StringBuilder sb) {
		sb.append("<?xml version=\"1.0\" encoding=\"UTF-8\"?>").append(System.lineSeparator());
		sb.append("<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns/graphml\"").append(System.lineSeparator());
		sb.append("xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\"").append(System.lineSeparator());
		sb.append("xsi:schemaLocation=\"http://graphml.graphdrawing.org/xmlns/graphml\">").append(System.lineSeparator());

		appendKeyLine(sb, "sourcecodelang", "string", "graph","sourcecodelang");
		appendKeyLine(sb, "creationTime", "string", "graph", "creationTime");
		appendKeyLine(sb, "witness-type", "string", "graph","witness-type");
		appendKeyLine(sb, "startline", "string", "edge","startline");
		appendKeyLine(sb, "assumption", "string", "edge","assumption");
		appendKeyLine(sb, "control", "string", "edge","control");
		appendKeyLine(sb, "stmt", "string", "edge","stmt");
		appendKeyLine(sb, "producer", "string","graph","producer");
		appendKeyLine(sb, "architecture", "string","graph","architecture");
		appendKeyLine(sb, "programHash", "string", "graph", "programhash");
		appendKeyLine(sb, "specification", "string", "graph", "specification");

		if(isViolationWitness) {
			appendKeyWithDefaultValue(sb, "entry", "string", "node", "entry", "false");
			appendKeyWithDefaultValue(sb, "violation", "string", "node", "violation", "false");
		} else {
			appendKeyWithDefaultValue(sb, "invariant", "string", "node", "invariant", "true");
		}

	}

	private void appendKeyLine(StringBuilder sb, String attrName, String attrType, String forElement, String id) {
		sb.append("<key attr.name=\"");
		sb.append(attrName);
		sb.append("\" attr.type=\"");
		sb.append(attrType);
		sb.append("\" for=\"");
		sb.append(forElement);
		sb.append("\" id=\"");
		sb.append(id);
		sb.append("\"/>");
		sb.append(System.lineSeparator());
	}

	private void appendKeyWithDefaultValue(StringBuilder sb, String attrName, String attrType, String forElement, String id, String defaultValue) {
		sb.append("<key attr.name=\"");
		sb.append(attrName);
		sb.append("\" attr.type=\"");
		sb.append(attrType);
		sb.append("\" for=\"");
		sb.append(forElement);
		sb.append("\" id=\"");
		sb.append(id);
		sb.append("\">");
		sb.append(System.lineSeparator());
		sb.append("\t<default>");
		sb.append(defaultValue);
		sb.append("</default>\n");
		sb.append(System.lineSeparator());
		sb.append("</key>");
		sb.append(System.lineSeparator());
	}

	private void printNode(final Node node, final StringBuilder sb) {
		if(node.getAttributes().getLabel().equals("")) {
			sb.append("<node id=\"").append(node.getId()).append("\"/>").append(System.lineSeparator());
		} else {
			sb.append("<node id=\"").append(node.getId()).append("\">").append(System.lineSeparator());
			sb.append(node.getAttributes().getLabel()).append(System.lineSeparator()); // TODO tabs?
			sb.append("</node>").append(System.lineSeparator());
		}
	}

	private void printEdges(final Node node, final StringBuilder sb) {
		for (final Edge edge : node.getOutEdges()) {
			sb.append("<edge source=\"").append(edge.getSource().getId());
			sb.append("\" target=\"").append(edge.getTarget().getId()).append(">").append(System.lineSeparator());
			sb.append(edge.getAttributes().getLabel()).append(System.lineSeparator()); // TODO tabs?
			sb.append("</edge>").append(System.lineSeparator());
		}
	}

	private static String createTaskHash(String programFile) {
		MessageDigest md = null;
		try {
			md = MessageDigest.getInstance("SHA256");
		} catch (NoSuchAlgorithmException e) {
			e.printStackTrace();
		}
		try (InputStream is = Files.newInputStream(Paths.get(programFile));
			 DigestInputStream dis = new DigestInputStream(is, md))
		{
			while (dis.read() != -1) {
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
		assert md != null;
		byte[] digest = md.digest();
		return bytesToHex(digest);
	}

	// source: https://www.baeldung.com/sha-256-hashing-java
	private static String bytesToHex(byte[] hash) {
		StringBuilder hexString = new StringBuilder(2 * hash.length);
		for (int i = 0; i < hash.length; i++) {
			String hex = Integer.toHexString(0xff & hash[i]);
			if(hex.length() == 1) {
				hexString.append('0');
			}
			hexString.append(hex);
		}
		return hexString.toString();
	}
}
