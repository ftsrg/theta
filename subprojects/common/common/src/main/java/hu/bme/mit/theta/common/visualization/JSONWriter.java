/*
 *  Copyright 2023 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.common.visualization.writer;

import hu.bme.mit.theta.common.visualization.*;

import java.awt.*;

public final class JSONWriter extends AbstractGraphWriter {

    private JSONWriter() {
    }

    private static class LazyHolder {
        static final JSONWriter INSTANCE = new JSONWriter();
    }

    public static JSONWriter getInstance() {
        return JSONWriter.LazyHolder.INSTANCE;
    }

    @Override
    public String writeString(Graph graph) {

        final StringBuilder sb = new StringBuilder();
        sb.append("{").append(System.lineSeparator());
        sb.append('\t').append("\"graph\": {").append(System.lineSeparator());
        sb.append('\t').append('\t').append("\"directed\": true,").append(System.lineSeparator());
        sb.append('\t').append('\t').append("\"type\": \"arg\",").append(System.lineSeparator());
        sb.append('\t').append('\t').append("\"nodes\": {");
        graph.getRootNodes().forEach(n -> printNode(n, sb));
        sb.deleteCharAt(sb.length() - 1).append(System.lineSeparator());
        sb.append('\t').append('\t').append("},").append(System.lineSeparator());

        sb.append('\t').append('\t').append("\"edges\": [");
        for (final Node node : graph.getNodes()) {
            printEdges(node, sb);
        }
        sb.deleteCharAt(sb.length() - 1).append(System.lineSeparator());
        sb.append('\t').append('\t').append("]").append(System.lineSeparator());

        sb.append('\t').append("}").append(System.lineSeparator());
        sb.append("}");

        return sb.toString();
    }

    private void printEdges(Node node, StringBuilder sb) {
        if (node instanceof CompositeNode) {
            if (node.getOutEdges().size() != 0) {
                throw new UnsupportedOperationException("Composite nodes have outgoing edges. Not supported ?");
            }
        } else {
            for (final Edge edge : node.getOutEdges()) {
                final EdgeAttributes attributes = edge.getAttributes();
                StringBuilder meta = new StringBuilder();
                meta.append("\"color\": \"").append(mapColorToString(attributes.getColor())).append("\", ");
                meta.append("\"style\": \"").append(attributes.getLineStyle().toString()).append("\", ");
                meta.append("\"weight\": \"").append(attributes.getWeight()).append("\", ");
                meta.append("\"font\": \"").append(attributes.getFont()).append("\", ");
                meta.append("\"align\": \"").append(attributes.getAlignment().toString()).append("\", ");
                meta.deleteCharAt(meta.length() - 1);
                meta.deleteCharAt(meta.length() - 1);

                sb.append(System.lineSeparator()).append("\t\t\t{");
                sb.append(System.lineSeparator()).append("\t\t\t\t\"label\": \"").append(convertLabel(attributes.getLabel())).append("\",");
                sb.append(System.lineSeparator()).append("\t\t\t\t\"source\": \"").append(edge.getSource().getId()).append("\",");
                sb.append(System.lineSeparator()).append("\t\t\t\t\"target\": \"").append(edge.getTarget().getId()).append("\",");
                sb.append(System.lineSeparator()).append("\t\t\t\t\"metadata\": { ").append(meta).append(" }");
                sb.append(System.lineSeparator()).append("\t\t\t},");
            }
        }
    }

    private void printNode(final Node node, final StringBuilder sb) {
        final NodeAttributes attributes = node.getAttributes();

        sb.append(System.lineSeparator()).append("\t\t\t\"").append(node.getId()).append("\": {").append(System.lineSeparator());
        sb.append("\t\t\t\t\"label\": \"").append(this.convertLabel(attributes.getLabel())).append("\",").append(System.lineSeparator());

        StringBuilder meta = new StringBuilder();
        meta.append("\"style\": \"").append(attributes.getLineStyle().toString()).append("\", ");
        meta.append("\"color\": \"").append(mapColorToString(attributes.getLineColor())).append("\", ");
        meta.append("\"fill\": \"").append(mapColorToString(attributes.getFillColor())).append("\", ");
        meta.append("\"font\": \"").append(attributes.getFont()).append("\", ");
        meta.append("\"align\": \"").append(attributes.getAlignment().toString()).append("\", ");
        meta.append("\"shape\": \"").append(attributes.getShape().toString()).append("\", ");
        meta.append("\"peripheries\": \"").append(attributes.getPeripheries()).append("\", ");
        meta.deleteCharAt(meta.length() - 1);
        meta.deleteCharAt(meta.length() - 1);

        sb.append("\t\t\t\t\"metadata\": { ").append(meta).append(" }").append(System.lineSeparator());

        sb.append("\t\t\t").append("},");
    }

    private String convertLabel(final String label) {
        return label.replaceAll("\\r\\n|\\r|\\n", " ");
    }

    private String mapColorToString(final Color color) {
        return String.format("#%02X%02X%02X", color.getRed(), color.getGreen(), color.getBlue());
    }
}
