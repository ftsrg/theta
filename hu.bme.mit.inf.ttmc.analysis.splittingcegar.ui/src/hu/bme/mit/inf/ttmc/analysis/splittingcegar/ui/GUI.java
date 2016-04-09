package hu.bme.mit.inf.ttmc.analysis.splittingcegar.ui;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.IOException;
import java.text.SimpleDateFormat;
import java.util.Arrays;
import java.util.Date;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JComboBox;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSpinner;
import javax.swing.JTabbedPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.SpinnerNumberModel;
import javax.swing.SwingWorker;
import javax.swing.UIManager;

import hu.bme.mit.inf.ttmc.aiger.impl.AIGERLoaderSimple;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.ClusteredCEGARBuilder;
import hu.bme.mit.inf.ttmc.cegar.common.CEGARLoop;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.GraphVizVisualizer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.YedVisualizer;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.InterpolatingCEGARBuilder;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.InterpolatingCEGARBuilder.InterpolationMethod;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.VisibleCEGARBuilder;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.VisibleCEGARBuilder.VarCollectionMethod;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.constraint.z3.Z3ConstraintManager;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSManagerImpl;
import hu.bme.mit.inf.ttmc.system.ui.SystemModel;
import hu.bme.mit.inf.ttmc.system.ui.SystemModelCreator;
import hu.bme.mit.inf.ttmc.system.ui.SystemModelLoader;

public class GUI extends JFrame {
	private static final long serialVersionUID = 5481134854291548278L;

	private enum VisType {
		None, yED, GraphViz
	};

	private enum Algorithm {
		Clustered, Visible, Interpolating
	};

	// Controls
	private final TwoColumnPanel pnl_controls;
	private final JComboBox<Algorithm> cb_algorithm;
	private final JSpinner sp_loglevel, sp_visLevel;
	private final JComboBox<VisType> cb_visType;
	private final JCheckBox cb_usecnf, cb_collectFromCond, cb_collectFromProp;
	private final JCheckBox cb_incrMC;
	private final JTextField txt_explVars;
	private final JCheckBox cb_debug;
	private final JComboBox<InterpolationMethod> cb_itpMethod;
	private final JComboBox<VarCollectionMethod> cb_varCollMethod;
	private final JTabbedPane tp_main;
	private final JTextArea txt_sts;
	private final JTextArea txt_out;

	private final Map<Component, Algorithm[]> algorithmSpecificSettings;

	String stsPath;
	String stsString;

	public GUI() {
		super("CEGAR");
		algorithmSpecificSettings = new HashMap<>();
		// Set look and feel
		try {
			UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName());
		} catch (final Exception e) {
		}
		// Initialize controls
		final JButton btn_loadSystem = new JButton("Load system");
		btn_loadSystem.addActionListener(new LoadSystemListener());
		final JButton btn_runCegar = new JButton("Run CEGAR");
		btn_runCegar.addActionListener(new RunCegarListener());
		final JLabel lbl_settings = new JLabel("Settings");
		lbl_settings.setPreferredSize(new Dimension(0, 30));
		lbl_settings.setVerticalAlignment(JLabel.BOTTOM);
		lbl_settings.setBorder(BorderFactory.createMatteBorder(0, 0, 1, 0, Color.BLACK));
		cb_algorithm = new JComboBox<>();
		cb_algorithm.addItem(Algorithm.Clustered);
		cb_algorithm.addItem(Algorithm.Visible);
		cb_algorithm.addItem(Algorithm.Interpolating);
		cb_algorithm.addActionListener(new AlgorithmChangedListener());
		cb_algorithm.setSelectedIndex(2);
		sp_loglevel = new JSpinner(new SpinnerNumberModel(2, 0, 10, 1));
		sp_visLevel = new JSpinner(new SpinnerNumberModel(10, 0, 10, 1));
		cb_visType = new JComboBox<>();
		cb_visType.addItem(VisType.None);
		cb_visType.addItem(VisType.GraphViz);
		cb_visType.addItem(VisType.yED);
		cb_usecnf = new JCheckBox("CNF transformation");
		algorithmSpecificSettings.put(cb_usecnf, new Algorithm[] { Algorithm.Visible, Algorithm.Interpolating });
		cb_collectFromCond = new JCheckBox("Collect predicates from conditions");
		algorithmSpecificSettings.put(cb_collectFromCond, new Algorithm[] { Algorithm.Interpolating });
		cb_collectFromProp = new JCheckBox("Collect predicates from property");
		algorithmSpecificSettings.put(cb_collectFromProp, new Algorithm[] { Algorithm.Interpolating });
		cb_incrMC = new JCheckBox("Incremental model checking");
		algorithmSpecificSettings.put(cb_incrMC, new Algorithm[] { Algorithm.Interpolating });
		cb_incrMC.setSelected(true);
		txt_explVars = new JTextField(10);
		algorithmSpecificSettings.put(txt_explVars, new Algorithm[] { Algorithm.Interpolating });
		cb_itpMethod = new JComboBox<>();
		cb_itpMethod.addItem(InterpolationMethod.Craig);
		cb_itpMethod.addItem(InterpolationMethod.Sequence);
		algorithmSpecificSettings.put(cb_itpMethod, new Algorithm[] { Algorithm.Interpolating });
		cb_varCollMethod = new JComboBox<>();
		cb_varCollMethod.addItem(VarCollectionMethod.CraigItp);
		cb_varCollMethod.addItem(VarCollectionMethod.SequenceItp);
		cb_varCollMethod.addItem(VarCollectionMethod.UnsatCore);
		algorithmSpecificSettings.put(cb_varCollMethod, new Algorithm[] { Algorithm.Visible });
		cb_debug = new JCheckBox("Debug mode");
		// Initialize output controls
		tp_main = new JTabbedPane();
		txt_out = new JTextArea(10, 60);
		txt_out.setFont(new Font("Consolas", Font.PLAIN, 11));
		txt_out.setEditable(false);
		txt_sts = new JTextArea(10, 60);
		txt_sts.setTabSize(3);
		txt_sts.setFont(txt_out.getFont());
		txt_sts.setEditable(false);
		tp_main.add("STS", new JScrollPane(txt_sts));
		tp_main.add("Output", new JScrollPane(txt_out));

		// Add controls to the main form
		pnl_controls = new TwoColumnPanel();
		pnl_controls.addControl(btn_loadSystem, btn_runCegar);
		pnl_controls.addControl(lbl_settings);
		pnl_controls.addControl("Algorithm:", cb_algorithm);
		pnl_controls.addControl("Level of logging:", sp_loglevel);
		pnl_controls.addControl("Visualization:", cb_visType);
		pnl_controls.addControl("Level of visualization:", sp_visLevel);
		pnl_controls.addControl(cb_usecnf);
		pnl_controls.addControl(cb_collectFromCond);
		pnl_controls.addControl(cb_collectFromProp);
		pnl_controls.addControl(cb_incrMC);
		pnl_controls.addControl("Explicit variables:", txt_explVars);
		pnl_controls.addControl("Interpolation method:", cb_itpMethod);
		pnl_controls.addControl("Variable collection:", cb_varCollMethod);
		pnl_controls.addControl(cb_debug);

		this.setLayout(new BorderLayout());
		final JPanel temp = new JPanel(new FlowLayout());
		temp.add(pnl_controls);
		this.add(temp, BorderLayout.WEST);
		this.add(tp_main, BorderLayout.CENTER);

		this.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		this.pack();
		this.setMinimumSize(new Dimension(500, 350));
		this.setSize(800, 500);

		stsPath = null;
		enableSpecificControls();
	}

	/**
	 * Listener for the 'Load system' button
	 */
	private final class LoadSystemListener implements ActionListener {
		@Override
		public void actionPerformed(final ActionEvent arg0) {
			final JFileChooser jfc = new JFileChooser();
			if (jfc.showOpenDialog(GUI.this) == JFileChooser.APPROVE_OPTION) {
				pnl_controls.setEnabledRecursive(false);
				new SwingWorker<Void, Void>() {
					@Override
					protected Void doInBackground() {
						stsPath = jfc.getSelectedFile().getAbsolutePath();
						try {
							stsString = loadSystem().toString();
						} catch (final Exception ex) {
							stsPath = null;
							stsString = "";
						}
						return null;
					}

					@Override
					protected void done() {
						txt_sts.setText("");
						txt_out.setText("");
						if (stsPath != null)
							txt_sts.setText(stsString);
						else
							error("Error opening " + jfc.getSelectedFile().getName() + ".");
						pnl_controls.setEnabledRecursive(true);
						enableSpecificControls();
					}
				}.execute();
			}
		}

	}

	/**
	 * Listener for the 'Run CEGAR' button
	 */
	private final class RunCegarListener implements ActionListener {
		@Override
		public void actionPerformed(final ActionEvent e) {
			if (stsPath != null) {
				txt_out.setText("");
				pnl_controls.setEnabledRecursive(false);
				tp_main.setSelectedIndex(1);
				new CegarWorker().execute();
			}
		}
	}

	/**
	 * Background worker for running the algorithm
	 */
	private final class CegarWorker extends SwingWorker<Void, String> implements Logger {
		@Override
		protected Void doInBackground() {
			CEGARLoop cegar = null;
			final String dateStr = new SimpleDateFormat("yyyyMMddHHmmssSSS").format(new Date());
			Visualizer visualizer = null;
			Visualizer debugVisualizer = null;
			if (cb_debug.isSelected())
				debugVisualizer = new GraphVizVisualizer(".", "debug_" + dateStr, 100, true);
			if (cb_visType.getSelectedItem().equals(VisType.GraphViz))
				visualizer = new GraphVizVisualizer(".", "vis_" + dateStr, (int) sp_visLevel.getValue());
			else if (cb_visType.getSelectedItem().equals(VisType.yED))
				visualizer = new YedVisualizer(".", "vis_" + dateStr, (int) sp_visLevel.getValue());
			// Build algorithm
			switch (cb_algorithm.getSelectedIndex()) {
			case 0:
				cegar = new ClusteredCEGARBuilder().visualizer(visualizer).debug(debugVisualizer).logger(this).build();
				break;
			case 1:
				cegar = new VisibleCEGARBuilder().visualizer(visualizer).debug(debugVisualizer).logger(this).useCNFTransformation(cb_usecnf.isSelected())
						.varCollectionMethod((VarCollectionMethod) cb_varCollMethod.getSelectedItem()).build();
				break;
			case 2:
				final InterpolatingCEGARBuilder builder = new InterpolatingCEGARBuilder().visualizer(visualizer).logger(this).debug(debugVisualizer)
						.useCNFTransformation(cb_usecnf.isSelected()).collectFromConditions(cb_collectFromCond.isSelected())
						.interpolationMethod((InterpolationMethod) cb_itpMethod.getSelectedItem()).collectFromSpecification(cb_collectFromProp.isSelected())
						.incrementalModelChecking(cb_incrMC.isSelected());
				if (!txt_explVars.getText().equals(""))
					for (final String var : txt_explVars.getText().split(","))
						builder.explicitVar(var);

				cegar = builder.build();
				break;
			}
			// Run algorithm
			if (cegar != null) {
				publish("Executing " + cegar + "\n");
				try {
					final STS sts = loadSystem();
					cegar.check(sts);
				} catch (final Exception e) {
					publish("An error occured:\n" + e.getMessage());
					e.printStackTrace();
				}
			}
			return null;
		}

		@Override
		protected void done() {
			pnl_controls.setEnabledRecursive(true);
			enableSpecificControls();
		}

		@Override
		protected void process(final List<String> chunks) {
			for (final String str : chunks)
				txt_out.append(str);
		}

		@Override
		public void write(final Object obj, final int level) {
			write(obj, level, 0);
		}

		@Override
		public void write(final Object obj, final int level, final int padding) {
			if (level <= (int) sp_loglevel.getValue()) {
				for (int i = 0; i < padding; ++i)
					publish("   ");
				publish(obj.toString());
			}
		}

		@Override
		public void writeln(final int level) {
			if (level <= (int) sp_loglevel.getValue())
				publish("\n");
		}

		@Override
		public void writeln(final Object obj, final int level) {
			writeln(obj, level, 0);
		}

		@Override
		public void writeln(final Object obj, final int level, final int padding) {
			write(obj, level, padding);
			writeln(level);
		}

		@Override
		public void writeHeader(final Object obj, final int level) {
			if (level <= (int) sp_loglevel.getValue()) {
				publish("\n");
				publish("----------" + obj + "----------\n");
			}
		}
	}

	private final class AlgorithmChangedListener implements ActionListener {

		@Override
		public void actionPerformed(final ActionEvent arg0) {
			enableSpecificControls();
		}

	}

	private void error(final String message) {
		JOptionPane.showMessageDialog(GUI.this, message, "Error", JOptionPane.ERROR_MESSAGE);
	}

	private STS loadSystem() throws IOException {
		STS sts = null;
		final STSManager manager = new STSManagerImpl(new Z3ConstraintManager());
		if (stsPath.endsWith(".system")) {
			final SystemModel systemModel = SystemModelCreator.create(manager, SystemModelLoader.getInstance().load(stsPath));
			assert (systemModel.getSTSs().size() == 1);
			sts = systemModel.getSTSs().iterator().next();
		} else if (stsPath.endsWith(".aag")) {
			sts = new AIGERLoaderSimple().load(stsPath, manager);
		}
		return sts;
	}

	private void enableSpecificControls() {
		for (final Component comp : algorithmSpecificSettings.keySet()) {
			comp.setEnabled(Arrays.asList(algorithmSpecificSettings.get(comp)).contains(cb_algorithm.getSelectedItem()));
		}
	}
}
