/*
 * Copyright 2021 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package hu.bme.mit.theta.xcfa.cli.stateless;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;
import hu.bme.mit.theta.xcfa.model.XcfaStackFrame;
import hu.bme.mit.theta.xcfa.model.XcfaState;

import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.ScrollPaneConstants;
import javax.swing.WindowConstants;
import javax.swing.border.LineBorder;
import javax.swing.border.MatteBorder;
import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.GridBagLayout;
import java.awt.RenderingHints;
import java.awt.Toolkit;
import java.util.Date;
import java.util.List;

public class XcfaGui extends JFrame {
	private final XcfaState state;

	private static final int width = 1680;
	private static final int height = 1050;
	private static final String title = "XCFA (Theta)";

	private JTextArea logTextArea;
	private JComponent visualizationPanel;

	public XcfaGui(XCFA xcfa) {
		this.state = xcfa.getInitialState();
		this.setSize(width, height);
		this.setResizable(false);
		Dimension screenSize = Toolkit.getDefaultToolkit().getScreenSize();
		this.setLocation(screenSize.width / 2 - width/2, screenSize.height / 2 - height/2);
		this.setTitle(title);
		this.setDefaultCloseOperation(WindowConstants.EXIT_ON_CLOSE);
		JComponent mainPanel = createMainPanel();
		addThread("main", xcfa.getMainProcess());
		this.setContentPane(mainPanel);
		this.setVisible(true);
	}

	private void log(String msg) {
		logTextArea.append(new Date().toString() + "\t" + msg + "\n");
	}

	private void addThread(String name, XcfaProcess process) {
		JPanel jPanel = new JPanel();
		jPanel.setPreferredSize(new Dimension(width/4, 0));
		jPanel.setMaximumSize(new Dimension(width/4, 3*height/4));
		jPanel.setBorder(new LineBorder(Color.BLACK));

		jPanel.setLayout(new BoxLayout(jPanel, BoxLayout.Y_AXIS));
		AALabel jLabel = new AALabel(name, Color.BLACK, -1);
		JPanel namePanel = new JPanel();
		namePanel.setLayout(new GridBagLayout());
		namePanel.add(jLabel);
		namePanel.setPreferredSize(new Dimension(width/4, 16));

		jPanel.add(namePanel);
		jPanel.add(createVariablePanel(process));
		jPanel.add(visualizeChoices(process));
		jPanel.add(createTraceLogPanel());

		visualizationPanel.add(jPanel);
		visualizationPanel.revalidate();
	}

	private static class AALabel extends JLabel {
		public AALabel(String s, Color color, int i) {
			super((i > 0 && s.length() > i) ? (s.substring(0, i-2) + "...") : s);
			this.setToolTipText(s);
			this.setForeground(color);
			this.setBorder(BorderFactory.createEmptyBorder(3, 5, 3, 5));
		}
		@Override
		public void paint(Graphics g) {
			((Graphics2D)g).setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING,RenderingHints.VALUE_TEXT_ANTIALIAS_LCD_HRGB);
			super.paint(g);
		}
	}
	private static class AAButton extends JButton {
		public AAButton(String s) {
			super(s);
		}
		@Override
		public void paint(Graphics g) {
			((Graphics2D)g).setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING,RenderingHints.VALUE_TEXT_ANTIALIAS_LCD_HRGB);
			super.paint(g);
		}
	}
	private static class AATextArea extends JTextArea {
		@Override
		public void paint(Graphics g) {
			((Graphics2D)g).setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING,RenderingHints.VALUE_TEXT_ANTIALIAS_LCD_HRGB);
			super.paint(g);
		}
	}

	private int varLines = 0;
	private void addVariable(JPanel jPanel, XcfaProcedure proc, VarDecl<?> var) {
		JPanel varPanel = new JPanel();
		if(varLines++ % 2 == 0) varPanel.setBackground(Color.LIGHT_GRAY);
		varPanel.setLayout(new BoxLayout(varPanel, BoxLayout.X_AXIS));
		varPanel.add(new AALabel((proc == null ? "" : (proc.getName() + ".")) + var.getName(), Color.BLACK, -1));
		varPanel.add(new AALabel(" [" + var.getType().toString() + "] ", Color.GRAY, -1));
		varPanel.add(Box.createHorizontalGlue());
		varPanel.add(new AALabel("-1", Color.BLACK, -1));
		jPanel.add(varPanel);
	}

	private JComponent createVariablePanel(XcfaProcess process) {
		JPanel jPanel = new JPanel();
		JScrollPane jScrollPane = new JScrollPane(jPanel);
		jPanel.setLayout(new BoxLayout(jPanel, BoxLayout.Y_AXIS));
		jScrollPane.setVerticalScrollBarPolicy(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED);
		jScrollPane.setHorizontalScrollBarPolicy(ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
		jScrollPane.setPreferredSize(new Dimension(width/4, 3*height/12 - 20));
		for (VarDecl<?> threadLocalVar : process.getThreadLocalVars()) {
			addVariable(jPanel, null, threadLocalVar);
		}
		for (XcfaProcedure procedure : process.getProcedures()) {
			for (VarDecl<?> localVar : procedure.getLocalVars()) {
				addVariable(jPanel, procedure, localVar);
			}
		}
		return jScrollPane;
	}



	private int traceLines = 0;
	private void addTraceLine(JPanel jPanel, XcfaEdge edge) {
		JPanel tracePanel = new JPanel();
		if(traceLines++ % 2 == 0) tracePanel.setBackground(Color.LIGHT_GRAY);
		tracePanel.setLayout(new BoxLayout(tracePanel, BoxLayout.X_AXIS));
		tracePanel.add(new AALabel(edge.getSource().getName(), Color.BLACK, -1));
		tracePanel.add(Box.createHorizontalGlue());
		tracePanel.add(new AALabel(" -> ", Color.GRAY, -1));
		tracePanel.add(Box.createHorizontalGlue());
		tracePanel.add(new AALabel(edge.getTarget().getName(), Color.BLACK, -1));
		jPanel.add(tracePanel);
	}

	private JComponent createTraceLogPanel() {
		JPanel jPanel = new JPanel();
		JScrollPane jScrollPane = new JScrollPane(jPanel);
		jPanel.setLayout(new BoxLayout(jPanel, BoxLayout.Y_AXIS));
		jScrollPane.setVerticalScrollBarPolicy(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED);
		jScrollPane.setHorizontalScrollBarPolicy(ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
		jScrollPane.setPreferredSize(new Dimension(width/4, 3*height/12 - 20));
		addTraceLine(jPanel, new XcfaEdge(new XcfaLocation("Loc", null), new XcfaLocation("Loc" + 1, null), List.of()));
		return jScrollPane;
	}

	private JComponent visualizeChoices(XcfaProcess process) {
		JPanel jPanel = new JPanel();
		JScrollPane jScrollPane = new JScrollPane(jPanel);
		jPanel.setLayout(new BoxLayout(jPanel, BoxLayout.Y_AXIS));
		jScrollPane.setVerticalScrollBarPolicy(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED);
		jScrollPane.setHorizontalScrollBarPolicy(ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
		jScrollPane.setPreferredSize(new Dimension(width/4, 3*height/12 - 20));
		for (XcfaStackFrame xcfaStackFrame : state.getOffers().get(process)) {
			addChoice(jPanel, xcfaStackFrame);
		}
		return jScrollPane;
	}

	private void addChoice(JPanel jPanel, XcfaStackFrame xcfaStackFrame) {
		XcfaEdge edge = xcfaStackFrame.getEdge();
		int i = edge.getStmts().indexOf(xcfaStackFrame.getStmt());
		JPanel choice = new JPanel();
		choice.setLayout(new BorderLayout());
		choice.add(new AALabel(edge.getSource().getName(), Color.BLACK, -1), BorderLayout.LINE_START);
		JPanel expressions = new JPanel();
		expressions.setLayout(new BoxLayout(expressions, BoxLayout.Y_AXIS));
		int cnt = 0;
		for (Stmt stmt : edge.getStmts()){
			JPanel stmtpanel = new JPanel();
			stmtpanel.setLayout(new BoxLayout(stmtpanel, BoxLayout.X_AXIS));
			stmtpanel.add(new AALabel(stmt.toString(), Color.BLUE, 40));
			stmtpanel.add(Box.createHorizontalGlue());
			if(cnt++ == i) {
				AAButton choose = new AAButton("Choose");
				stmtpanel.add(choose);
				choose.addActionListener(actionEvent -> {
					xcfaStackFrame.accept();
					addThread("main2", state.getXcfa().getMainProcess());
				} );
			}
			expressions.add(stmtpanel);
		}
		expressions.setBorder(new MatteBorder(0,1,0,1,Color.GRAY));
		choice.add(expressions, BorderLayout.CENTER);
		choice.add(new AALabel(edge.getTarget().getName(), Color.BLACK, -1), BorderLayout.LINE_END);
		choice.setMaximumSize(new Dimension(width/4 - 10, 25));
		choice.setBorder(LineBorder.createBlackLineBorder());
		jPanel.add(choice);
	}

	private JComponent createMainPanel() {
		JPanel jPanel = new JPanel();
		jPanel.setLayout(new BorderLayout());

		jPanel.add(createSettingsPanel(), BorderLayout.LINE_START);
		jPanel.add(createVisualizationPanel(), BorderLayout.CENTER);
		jPanel.add(createLogPanel(), BorderLayout.PAGE_END);

		return jPanel;
	}

	private JComponent createLogPanel() {
		logTextArea = new AATextArea();
		logTextArea.setEditable(false);
		JScrollPane jScrollPane = new JScrollPane(logTextArea);
		jScrollPane.setVerticalScrollBarPolicy(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED);
		jScrollPane.setHorizontalScrollBarPolicy(ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
		jScrollPane.setPreferredSize(new Dimension(0, height/4));
		return jScrollPane;
	}

	private JComponent createVisualizationPanel() {
		JPanel jPanel = new JPanel();
		JScrollPane jScrollPane = new JScrollPane(jPanel);
		jScrollPane.setVerticalScrollBarPolicy(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED);
		jScrollPane.setHorizontalScrollBarPolicy(ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
		jScrollPane.setPreferredSize(new Dimension(4*width / 5, 3*height/4));

		jPanel.setLayout(new BoxLayout(jPanel, BoxLayout.X_AXIS));
		return visualizationPanel = jPanel;
	}

	private JComponent createSettingsPanel() {
		JPanel jPanel = new JPanel();
		jPanel.setPreferredSize(new Dimension(width / 5, 3*height/4));
		return jPanel;
	}
}
