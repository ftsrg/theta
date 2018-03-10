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
package hu.bme.mit.theta.cfa.tool;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;

import com.google.common.base.Charsets;
import com.google.common.io.Files;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.CfaAction;
import hu.bme.mit.theta.cfa.analysis.CfaState;
import hu.bme.mit.theta.cfa.analysis.CfaTraceConcretizer;
import hu.bme.mit.theta.cfa.dsl.CfaDslManager;
import hu.bme.mit.theta.cfa.tool.CfaConfigBuilder.Domain;
import hu.bme.mit.theta.cfa.tool.CfaConfigBuilder.Encoding;
import hu.bme.mit.theta.cfa.tool.CfaConfigBuilder.InitPrec;
import hu.bme.mit.theta.cfa.tool.CfaConfigBuilder.PrecGranularity;
import hu.bme.mit.theta.cfa.tool.CfaConfigBuilder.PredSplit;
import hu.bme.mit.theta.cfa.tool.CfaConfigBuilder.Refinement;
import hu.bme.mit.theta.cfa.tool.CfaConfigBuilder.Search;
import hu.bme.mit.theta.cfa.utils.CfaVisualizer;
import hu.bme.mit.theta.common.BaseGui;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.TextAreaLogger;
import hu.bme.mit.theta.common.table.impl.HtmlTableWriter;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter.Format;
import javafx.application.Platform;
import javafx.concurrent.Task;
import javafx.scene.control.Button;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ChoiceBox;
import javafx.scene.control.Spinner;
import javafx.scene.control.Tab;
import javafx.scene.control.TextArea;
import javafx.scene.text.Font;
import javafx.scene.web.WebView;
import javafx.stage.FileChooser;
import javafx.stage.Stage;

/**
 * A graphical user interface for running a CEGAR configuration on a CFA.
 */
public class CfaGui extends BaseGui {
	private ChoiceBox<Domain> cbDomain;
	private ChoiceBox<Refinement> cbRefinement;
	private ChoiceBox<Search> cbSearch;
	private ChoiceBox<PredSplit> cbPredSplit;
	private ChoiceBox<PrecGranularity> cbPrecGranularity;
	private ChoiceBox<Encoding> cbEncoding;
	private Spinner<Integer> spMaxEnum;
	private ChoiceBox<InitPrec> cbInitPrec;
	private ChoiceBox<Logger.Level> cbLogLevel;
	private CheckBox cbStructureOnly;

	private TextArea taModel;
	private TextArea taOutput;
	private WebView wvVisualModel;
	private WebView wvVisualResult;

	private Tab tabModel;
	private Tab tabOutput;
	private Tab tabVisualModel;
	private Tab tabVisualResult;

	private SafetyResult<?, ?> safetyResult;

	@Override
	protected void initializeControls(final Stage primaryStage) {
		taModel = new TextArea();
		taModel.setFont(Font.font("Consolas"));

		wvVisualModel = new WebView();
		wvVisualModel.setOnScroll(
				evt -> wvVisualModel.setZoom((evt.getDeltaY() > 0 ? 1.1 : 1 / 1.1) * wvVisualModel.getZoom()));

		taOutput = new TextArea();
		taOutput.setEditable(false);

		wvVisualResult = new WebView();
		wvVisualResult.setOnScroll(
				evt -> wvVisualResult.setZoom((evt.getDeltaY() > 0 ? 1.1 : 1 / 1.1) * wvVisualResult.getZoom()));

		tabModel = createTab("Model Editor", taModel);
		tabVisualModel = createTab("Model Visualized", wvVisualModel);
		tabOutput = createTab("Console Output", taOutput);
		tabVisualResult = createTab("Result Visualized", wvVisualResult);

		createTitle("Input model");
		final Button btnLoadModel = createButton("Load CFA");
		btnLoadModel.setOnMouseClicked(e -> btnLoadClicked(primaryStage));
		final Button btnVisualizeModel = createButton("Visualize CFA");
		btnVisualizeModel.setOnMouseClicked(e -> btnVisualizeModelClicked());

		createTitle("Algorithm");
		cbDomain = createChoice("Domain", Domain.values());
		cbRefinement = createChoice("Refinement", Refinement.values());
		cbSearch = createChoice("Search", Search.values());
		cbPredSplit = createChoice("Predicate split", PredSplit.values());
		cbPrecGranularity = createChoice("Precision granularity", PrecGranularity.values());
		cbEncoding = createChoice("Encoding", Encoding.values());
		spMaxEnum = createSpinner("Max. succ. to enumerate", 0, Integer.MAX_VALUE, 0);
		cbInitPrec = createChoice("Initial precision", InitPrec.values());
		cbLogLevel = createChoice("Logging level", Logger.Level.values());

		final Button btnRunAlgo = createButton("Run algorithm");
		btnRunAlgo.setOnMouseClicked(e -> btnRunAlgoClicked());

		createTitle("Result");
		cbStructureOnly = createCheckBox("Structure only");
		final Button btnVisualizeResult = createButton("Visualize result");
		btnVisualizeResult.setOnMouseClicked(e -> btnVisualizeResultClicked());
	}

	private void clearModel() {
		taModel.clear();
		wvVisualModel.getEngine().loadContent("");
	}

	private void clearResult() {
		taOutput.clear();
		wvVisualResult.getEngine().loadContent("");
	}

	private void btnLoadClicked(final Stage stage) {
		final File fileToOpen = new FileChooser().showOpenDialog(stage);
		if (fileToOpen != null) {
			clearModel();
			clearResult();
			selectTab(tabModel);
			runBackgroundTask(new LoadFileTextTask(fileToOpen.getAbsolutePath(), taModel::setText));
		}
	}

	private void btnVisualizeModelClicked() {
		selectTab(tabVisualModel);
		runBackgroundTask(new VisualizeModelTask());
	}

	private void btnRunAlgoClicked() {
		clearResult();
		selectTab(tabOutput);
		runBackgroundTask(new RunAlgorithmTask());
	}

	private void btnVisualizeResultClicked() {
		selectTab(tabVisualResult);
		runBackgroundTask(new VisualizeResultTask());
	}

	private final class RunAlgorithmTask extends Task<Void> {
		@Override
		protected Void call() throws Exception {
			try {
				final CFA cfa = CfaDslManager.createCfa(taModel.getText());
				final Config<?, ?, ?> config = new CfaConfigBuilder(cbDomain.getValue(), cbRefinement.getValue())
						.search(cbSearch.getValue()).predSplit(cbPredSplit.getValue())
						.precGranularity(cbPrecGranularity.getValue()).encoding(cbEncoding.getValue())
						.maxEnum(spMaxEnum.getValue()).initPrec(cbInitPrec.getValue())
						.logger(new TextAreaLogger(cbLogLevel.getValue(), taOutput)).build(cfa);
				safetyResult = config.check();
			} catch (final Exception ex) {
				Platform.runLater(() -> displayException(ex));
			} finally {
				Platform.runLater(() -> disableControls(false));
			}
			return null;
		}
	}

	private final class VisualizeModelTask extends Task<Void> {

		@Override
		protected Void call() throws Exception {
			try {
				final CFA cfa = CfaDslManager.createCfa(taModel.getText());
				final Graph graph = CfaVisualizer.visualize(cfa);
				final File tmpFile = File.createTempFile("theta", ".tmp");
				GraphvizWriter.getInstance().writeFile(graph, tmpFile.getAbsolutePath(), Format.SVG);
				final String image = Files.asCharSource(tmpFile, Charsets.UTF_8).read();
				tmpFile.delete();
				Platform.runLater(() -> wvVisualModel.getEngine().loadContent(image));
			} catch (final Exception ex) {
				Platform.runLater(() -> displayException(ex));
			} finally {
				Platform.runLater(() -> disableControls(false));
			}
			return null;
		}

	}

	private final class VisualizeResultTask extends Task<Void> {

		@Override
		protected Void call() throws Exception {
			try {
				if (safetyResult == null) {
					throw new IllegalStateException("No result is present.");
				}
				String content = "";
				if (safetyResult.isSafe()) {
					Graph graph = null;
					if (cbStructureOnly.isSelected()) {
						graph = ArgVisualizer.getStructureOnly().visualize(safetyResult.asSafe().getArg());
					} else {
						graph = ArgVisualizer.getDefault().visualize(safetyResult.asSafe().getArg());
					}
					final File tmpFile = File.createTempFile("theta", ".tmp");
					GraphvizWriter.getInstance().writeFile(graph, tmpFile.getAbsolutePath(), Format.SVG);
					content = Files.asCharSource(tmpFile, Charsets.UTF_8).read();
					tmpFile.delete();
				} else {
					@SuppressWarnings("unchecked")
					final Trace<CfaState<?>, CfaAction> trace = (Trace<CfaState<?>, CfaAction>) safetyResult.asUnsafe()
							.getTrace();
					final ByteArrayOutputStream baos = new ByteArrayOutputStream();
					final PrintStream ps = new PrintStream(baos, true, "utf-8");
					CfaVisualizer.printTraceTable(CfaTraceConcretizer.concretize(trace), new HtmlTableWriter(ps));
					content = new String(baos.toByteArray(), StandardCharsets.UTF_8);
					ps.close();
				}

				final String finalContent = content;
				Platform.runLater(() -> wvVisualResult.getEngine().loadContent(finalContent));
			} catch (final Exception ex) {
				Platform.runLater(() -> displayException(ex));
			} finally {
				Platform.runLater(() -> disableControls(false));
			}
			return null;
		}

	}

	@Override
	protected String getTitle() {
		return "theta-cfa-gui";
	}

	public static void main(final String args[]) {
		launch(args);
	}
}
