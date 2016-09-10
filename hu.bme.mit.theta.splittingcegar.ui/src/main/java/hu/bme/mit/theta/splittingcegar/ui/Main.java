package hu.bme.mit.theta.splittingcegar.ui;

import java.io.FileNotFoundException;

public class Main {
	public static void main(final String[] args) throws FileNotFoundException {
		if (args.length == 0)
			new GUI().setVisible(true);
		else
			CLI.main(args);
	}
}
