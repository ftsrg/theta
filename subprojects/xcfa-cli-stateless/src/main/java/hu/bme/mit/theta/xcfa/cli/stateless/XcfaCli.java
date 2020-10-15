/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.cli.stateless;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;
import com.google.common.base.Stopwatch;
import hu.bme.mit.theta.mcm.MCM;
import hu.bme.mit.theta.mcm.dsl.McmDslManager;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.analysis.stateless.StatelessMC;
import hu.bme.mit.theta.xcfa.dsl.XcfaDslManager;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.concurrent.TimeUnit;

public class XcfaCli {
	private static final String JAR_NAME = "theta-xcfa-cli.jar";
	private final String[] args;

	@Parameter(names = "--model", description = "Path of the input XCFA model", required = true)
	String model;

	@Parameter(names = "--mcm", description = "Path of the input MCM model", required = true)
	String mcm;

	@Parameter(names = "--poolsize", description = "Size of the thread pool (1 by default)", required = false)
	Integer threadPoolSize = 1;

	@Parameter(names = "--print-cex", description = "Print counterexample as cex.dot", required = false)
	boolean printcex;

	@Parameter(names = "--all-states", description = "Print all resulting states as .dot files", required = false)
	boolean allstates;

	public XcfaCli(final String[] args) {
		this.args = args;
	}

	public static void main(final String[] args) {
		final XcfaCli mainApp = new XcfaCli(args);
		mainApp.run();
	}

	private void run() {
		try {
			JCommander.newBuilder().addObject(this).programName(JAR_NAME).build().parse(args);
		} catch (final ParameterException ex) {
			System.out.println("Invalid parameters, details:");
			System.out.println(ex.getMessage());
			ex.usage();
			return;
		}

		try {
			final Stopwatch sw = Stopwatch.createStarted();
			final XCFA xcfa = loadModel();
			final MCM mcm = loadMcm(xcfa);
			if(StatelessMC.check(xcfa, mcm, threadPoolSize, printcex, allstates)) {
				System.out.println("VERIFICATION SUCCESSFUL");
			}
			else {
				System.out.println("VERIFICATION FAILED");
			}
			sw.stop();
			System.out.println(sw.elapsed(TimeUnit.MILLISECONDS) + " ms");
		} catch (final Throwable ex) {
			ex.printStackTrace();
		}
	}

	private XCFA loadModel() throws IOException {
		try(InputStream inputStream = new FileInputStream(new File(model))) {
			return XcfaDslManager.createXcfa(inputStream);
		}
	}
	private MCM loadMcm(XCFA xcfa) throws IOException {
		try(InputStream inputStream = new FileInputStream(new File(mcm))) {
			return McmDslManager.createMCM(inputStream, xcfa.getProcesses(), xcfa.getGlobalVars());
		}
	}

}
