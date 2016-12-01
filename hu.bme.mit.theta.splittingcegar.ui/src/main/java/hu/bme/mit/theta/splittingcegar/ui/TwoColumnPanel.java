package hu.bme.mit.theta.splittingcegar.ui;

import java.awt.Component;
import java.awt.Container;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;

import javax.swing.JLabel;
import javax.swing.JPanel;

/**
 * A wrapper for a panel with two columns.
 */
public class TwoColumnPanel extends JPanel {
	private static final long serialVersionUID = -2335615291806885301L;

	private int controlNo = 0;

	public TwoColumnPanel() {
		this.setLayout(new GridBagLayout());
	}

	public void addControl(final Component control) {
		final GridBagConstraints c = new GridBagConstraints();
		c.fill = GridBagConstraints.HORIZONTAL;
		c.gridwidth = 2;
		c.gridx = 0;
		c.gridy = controlNo++;
		add(control, c);
	}

	public void addControl(final Component leftControl, final Component rightControl) {
		final GridBagConstraints c = new GridBagConstraints();
		c.fill = GridBagConstraints.HORIZONTAL;
		c.gridx = 0;
		c.gridy = controlNo++;
		add(leftControl, c);
		c.gridx = 1;
		add(rightControl, c);
	}

	public void addControl(final String leftLabel, final Component rightControl) {
		addControl(new JLabel(leftLabel + " "), rightControl);
	}

	public void setEnabledRecursive(final boolean isEnabled) {
		setEnabledRecursive(this, isEnabled);
	}

	private void setEnabledRecursive(final Component comp, final boolean isEnabled) {
		comp.setEnabled(isEnabled);
		if (comp instanceof Container)
			for (final Component child : ((Container) comp).getComponents())
				setEnabledRecursive(child, isEnabled);
	}
}
