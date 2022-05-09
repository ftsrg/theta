/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.algorithm.mcm;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.LitExpr;

import javax.swing.*;
import java.awt.*;
import java.awt.geom.Path2D;
import java.util.List;
import java.util.*;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

public class ExecutionGraphVisualizer implements Runnable{
    private final ExecutionGraph executionGraph;
    private final List<Map<Decl<?>, LitExpr<?>>> solutions;
    private int currentSolution = 0;
    private final Map<Integer, Tuple2<Double, Double>> events;
    private final double eventWidth, eventHeight;
    private final Map<String, Color> relations;
    private final Map<String, Integer> possibleRelations;
    private static final Set<String> alwaysShow = Set.of("rf", "R", "W", "F");

    public ExecutionGraphVisualizer(
            final ExecutionGraph executionGraph,
            final Collection<Map<Decl<?>, LitExpr<?>>> solutions,
            final List<List<Integer>> threadEvents,
            final List<Integer> initialWrites) {
        this.executionGraph = executionGraph;
        this.solutions = List.copyOf(solutions);
        this.events = new LinkedHashMap<>();
        int threadNum = Integer.max(threadEvents.size(), initialWrites.size());
        int instructionNum = threadEvents.stream().map(List::size).max(Integer::compareTo).get() + 1;
        double dX = 90.0 / (threadNum + 1);
        double dY = 90.0 / (instructionNum + 1);
        eventWidth = dX * 0.45;
        eventHeight = dY * 0.45;
        for (int i = 1; i <= threadEvents.size(); i++) {
            double x = i * dX + 5.0;
            for (int j = 1; j <= threadEvents.get(i-1).size(); j++) {
                double y = (j + 1) * dY + 5.0;
                events.put(threadEvents.get(i-1).get(j-1), Tuple2.of(x, y));
            }
        }
        for (int i = 1; i <= initialWrites.size(); i++) {
            double x = i * dX + 5.0;
            double y = 1 * dY + 5.0;
            events.put(initialWrites.get(i-1), Tuple2.of(x, y));
        }
        possibleRelations = new LinkedHashMap<>();
        for (Map<Decl<?>, LitExpr<?>> solution : solutions) {
            for (Decl<?> decl : solution.keySet()) {
                String[] s = decl.getName().split("_");
                possibleRelations.put(s[0], s.length-1);
            }
        }
        relations = new LinkedHashMap<>();
    }


    @Override
    public void run() {
        final JFrame frame = new JFrame("Execution Graph Visualizer - Theta");
        frame.setDefaultCloseOperation(WindowConstants.EXIT_ON_CLOSE);
        frame.setSize(1024, 768);
        final JPanel mainPanel = new JPanel(new BorderLayout());
        frame.setContentPane(mainPanel);

        JComboBox<Integer> solutionChooser = new JComboBox<>();
        for (int i = 0; i < solutions.size(); i++) {
            solutionChooser.addItem(i);
        }
        solutionChooser.addActionListener(actionEvent -> {
            currentSolution = solutionChooser.getSelectedIndex();
            frame.invalidate();
            frame.repaint();
        });
        mainPanel.add(solutionChooser, BorderLayout.NORTH);
        final JPanel relationPanel = new JPanel(new BorderLayout());
        relationPanel.setLayout(new BoxLayout(relationPanel, BoxLayout.PAGE_AXIS));
        JScrollPane scrollpanel = new JScrollPane(relationPanel,
                JScrollPane.VERTICAL_SCROLLBAR_ALWAYS,
                JScrollPane.HORIZONTAL_SCROLLBAR_NEVER);
        scrollpanel.getVerticalScrollBar().setUnitIncrement(16);
        final JPanel drawingPanel = new ExecutionGraphPanel();
        mainPanel.add(drawingPanel, BorderLayout.CENTER);
        possibleRelations.entrySet().stream().sorted(Map.Entry.comparingByKey()).forEach(entry -> {
            int arity = entry.getValue();
            String s = entry.getKey();
            JCheckBox jCheckBox = new JCheckBox(s);
            if(alwaysShow.contains(s)) {
                jCheckBox.setSelected(true);
                relations.put(s, getColor(s));
            }
            jCheckBox.addActionListener(actionEvent -> {
                if (jCheckBox.isSelected()) {
                    relations.put(s, getColor(s));
                } else {
                    relations.remove(s);
                }
                frame.invalidate();
                frame.repaint();
            });
            relationPanel.add(jCheckBox);
        });
        mainPanel.add(scrollpanel, BorderLayout.WEST);


        frame.setVisible(true);
        while(true) {
            try {
                Thread.sleep(1000);
            } catch (InterruptedException e) {
                throw new RuntimeException(e);
            }
        }
    }

    private Color getColor(String relation) {
        Random random = new Random(relation.hashCode());
        return switch(relation) {
            case "po" -> Color.BLACK;
            case "rf" -> Color.RED;
            case "co" -> Color.MAGENTA;
            default -> new Color(random.nextInt(256), random.nextInt(256), random.nextInt(256));
        };
    }

    private class ExecutionGraphPanel extends JPanel{
        @Override
        protected void paintComponent(Graphics g) {
            float strokeSize = Float.min(getWidth() / 100.0f / 4, getHeight() / 100.0f / 4);
            ((Graphics2D)g).setStroke(new BasicStroke(strokeSize));
            ((Graphics2D)g).setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
            ((Graphics2D)g).setRenderingHint(RenderingHints.KEY_STROKE_CONTROL, RenderingHints.VALUE_STROKE_PURE);
            double eventWidth = ExecutionGraphVisualizer.this.eventWidth * getWidth() / 100.0f;
            double eventHeight = ExecutionGraphVisualizer.this.eventHeight * getHeight() / 100.0f;
            solutions.get(currentSolution).forEach((decl, lit) -> {
                if(lit.equals(True())) {
                    String[] s = decl.getName().split("_");
                    if (relations.containsKey(s[0]) && s.length == 3) {
                        Tuple2<Double, Double> a = events.get(Integer.valueOf(s[1]));
                        Tuple2<Double, Double> b = events.get(Integer.valueOf(s[2]));
                        a = Tuple2.of(getWidth() / 100.0f * a.get1(), getHeight() / 100.0f * a.get2());
                        b = Tuple2.of(getWidth() / 100.0f * b.get1(), getHeight() / 100.0f * b.get2());
                        Color color = g.getColor();
                        g.setColor(relations.get(s[0]));
                        Path2D.Double path = new Path2D.Double();
                        double offset = Double.min(Math.abs(a.get1() - b.get1()),  Math.abs(a.get2() - b.get2())) * 0.1 * (0.8 + 0.4 * new Random(decl.hashCode()).nextDouble());
                        Tuple2<Double, Double> normal = Tuple2.of(a.get2() - b.get2(), b.get1() - a.get1());
                        double norm = Math.sqrt(normal.get1()*normal.get1() + normal.get2()*normal.get2());
                        normal = Tuple2.of(normal.get1() / norm, normal.get2() / norm);
                        Tuple2<Double, Double> dir = Tuple2.of(b.get1() - a.get1(), b.get2() - a.get2());
                        double dirnorm = Math.sqrt(dir.get1()*dir.get1() + dir.get2()*dir.get2());
                        dir = Tuple2.of(dir.get1() / dirnorm, dir.get2() / dirnorm);


                        a = Tuple2.of(a.get1() + dir.get1()*eventWidth/1.8, a.get2() + dir.get2()*eventHeight/1.8);
                        b = Tuple2.of(b.get1() - dir.get1()*eventWidth/1.8, b.get2() - dir.get2()*eventHeight/1.8);
                        Tuple2<Double, Double> midpoint = Tuple2.of(
                                (b.get1() + a.get1())/2 + offset * normal.get1(),
                                (b.get2() + a.get2())/2 + offset * normal.get2());

                        path.moveTo(a.get1(), a.get2());
                        path.curveTo(
                                a.get1(), a.get2(),
                                midpoint.get1(), midpoint.get2(),
                                b.get1(), b.get2()
                                );
                        Tuple2<Double, Double> derivative = Tuple2.of(2*b.get1() - 2*midpoint.get1(), 2*b.get2() - 2*midpoint.get2());
                        double derivativenorm = Math.sqrt(derivative.get1()*derivative.get1() + derivative.get2()*derivative.get2());
                        double arrowSize = strokeSize * 4;
                        derivative = Tuple2.of(derivative.get1() / derivativenorm * arrowSize, derivative.get2() / derivativenorm * arrowSize);

                        Tuple2<Double, Double> arrow1vec = vecRotated(derivative, Math.PI / 4);
                        Tuple2<Double, Double> arrow2vec = vecRotated(derivative, -Math.PI / 4);
                        path.moveTo(b.get1(), b.get2());
                        path.lineTo((b.get1() - arrow1vec.get1()), (b.get2() - arrow1vec.get2()));
                        path.moveTo(b.get1(), b.get2());
                        path.lineTo((b.get1() - arrow2vec.get1()), (b.get2() - arrow2vec.get2()));
                        

                        ((Graphics2D) g).draw(path);
                        g.setColor(color);
                    }
                }
            });
            events.forEach((integer, tuple) -> drawEvent((int) (getWidth() / 100.0f * tuple.get1()), (int) (getHeight() / 100.0f * tuple.get2()), g));
            solutions.get(currentSolution).forEach((decl, lit) -> {
                if(lit.equals(True())) {
                    String[] s = decl.getName().split("_");
                    if(relations.containsKey(s[0]) && s.length == 2) {
                        Tuple2<Double, Double> tuple = events.get(Integer.valueOf(s[1]));
                        Color color = g.getColor();
                        g.setColor(relations.get(s[0]));
                        drawLabelForEvent(s[0], (int) (getWidth() / 100.0f * tuple.get1()), (int) (getHeight() / 100.0f * tuple.get2()), g);
                        g.setColor(color);
                    }
                }
            });
        }

        private Tuple2<Double, Double> vecRotated(Tuple2<Double, Double> dir, double v) {
            return Tuple2.of(
                    dir.get1()*Math.cos(v)-dir.get2()*Math.sin(v),
                    dir.get1()*Math.sin(v)+dir.get2()*Math.cos(v));
        }

        private void drawLabelForEvent(String s, int x, int y, Graphics g) {
            ((Graphics2D)g).setFont(g.getFont().deriveFont(getWidth()/100.0f/4 * 15));
            FontMetrics fontMetrics = g.getFontMetrics();
            ((Graphics2D)g).setStroke(new BasicStroke(getWidth()/100.0f/4));
            g.drawString(s, x - fontMetrics.stringWidth(s) / 2, y + fontMetrics.getHeight()/4);
        }

        private void drawEvent(int x, int y, Graphics g) {
            double eventWidth = ExecutionGraphVisualizer.this.eventWidth * getWidth() / 100.0f;
            double eventHeight = ExecutionGraphVisualizer.this.eventHeight * getHeight() / 100.0f;
            g.setColor(Color.WHITE);
            ((Graphics2D)g).setStroke(new BasicStroke(Float.min(getWidth()/100.0f/2, getHeight()/100.0f/2)));
            g.fillOval((int) (x - eventWidth/2), (int) (y - eventHeight / 2), (int) eventWidth, (int) eventHeight);
            g.setColor(Color.BLACK);
            g.drawOval((int) (x - eventWidth/2), (int) (y - eventHeight / 2), (int) eventWidth, (int) eventHeight);
        }
    }
}
