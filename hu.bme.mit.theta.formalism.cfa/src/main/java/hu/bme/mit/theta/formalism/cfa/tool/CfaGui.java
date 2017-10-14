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
package hu.bme.mit.theta.formalism.cfa.tool;

import java.io.File;

import com.google.common.base.Charsets;
import com.google.common.io.Files;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.analysis.utils.TraceVisualizer;
import hu.bme.mit.theta.common.BaseGui;
import hu.bme.mit.theta.common.logging.impl.TextAreaLogger;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter.Format;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.analysis.CfaAction;
import hu.bme.mit.theta.formalism.cfa.analysis.CfaState;
import hu.bme.mit.theta.formalism.cfa.analysis.CfaTraceConcretizer;
import hu.bme.mit.theta.formalism.cfa.dsl.CfaDslManager;
import hu.bme.mit.theta.formalism.cfa.tool.CfaConfigBuilder.Domain;
import hu.bme.mit.theta.formalism.cfa.tool.CfaConfigBuilder.Encoding;
import hu.bme.mit.theta.formalism.cfa.tool.CfaConfigBuilder.PrecGranularity;
import hu.bme.mit.theta.formalism.cfa.tool.CfaConfigBuilder.PredSplit;
import hu.bme.mit.theta.formalism.cfa.tool.CfaConfigBuilder.Refinement;
import hu.bme.mit.theta.formalism.cfa.tool.CfaConfigBuilder.Search;
import hu.bme.mit.theta.formalism.cfa.utils.CfaVisualizer;
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

public class CfaGui extends BaseGui {
	private ChoiceBox<Domain> cbDomain;
	private ChoiceBox<Refinement> cbRefinement;
	private ChoiceBox<Search> cbSearch;
	private ChoiceBox<PredSplit> cbPredSplit;
	private ChoiceBox<PrecGranularity> cbPrecGranularity;
	private ChoiceBox<Encoding> cbEncoding;
	private Spinner<Integer> spLogLevel;
	private Button btnRunAlgo;
	private Button btnLoadModel;
	private Button btnVisualizeModel;
	private Button btnVisualizeResult;
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
		btnLoadModel = createButton("Load CFA");
		btnLoadModel.setOnMouseClicked(e -> btnLoadClicked(primaryStage));
		btnVisualizeModel = createButton("Visualize CFA");
		btnVisualizeModel.setOnMouseClicked(e -> btnVisualizeModelClicked());

		createTitle("Algorithm");
		cbDomain = createChoice("Domain", Domain.values());
		cbRefinement = createChoice("Refinement", Refinement.values());
		cbSearch = createChoice("Search", Search.values());
		cbPredSplit = createChoice("Predicate split", PredSplit.values());
		cbPrecGranularity = createChoice("Precision granularity", PrecGranularity.values());
		cbEncoding = createChoice("Encoding", Encoding.values());
		spLogLevel = createSpinner("Log level", 0, 100, 2);

		btnRunAlgo = createButton("Run algorithm");
		btnRunAlgo.setOnMouseClicked(e -> btnRunAlgoClicked());

		createTitle("Result");
		cbStructureOnly = createCheckBox("Structure only");
		btnVisualizeResult = createButton("Visualize result");
		btnVisualizeResult.setOnMouseClicked(e -> btnVisualizeResultClicked());
	}

	private void btnLoadClicked(final Stage stage) {
		final File result = new FileChooser().showOpenDialog(stage);
		if (result != null) {
			selectTab(tabModel);
			runBackgroundTask(new LoadFileTextTask(result.getAbsolutePath(), taModel::setText));
		}
	}

	private void btnVisualizeModelClicked() {
		selectTab(tabVisualModel);
		runBackgroundTask(new VisualizeModelTask());
	}

	private void btnRunAlgoClicked() {
		taOutput.clear();
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
						.logger(new TextAreaLogger(spLogLevel.getValue(), taOutput)).build(cfa);
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
				final String image = Files.toString(tmpFile, Charsets.UTF_8);
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
				Graph graph = null;
				if (safetyResult.isSafe()) {
					if (cbStructureOnly.isSelected()) {
						graph = ArgVisualizer.getStructureOnly().visualize(safetyResult.asSafe().getArg());
					} else {
						graph = ArgVisualizer.getDefault().visualize(safetyResult.asSafe().getArg());
					}
				} else {
					@SuppressWarnings("unchecked")
					final Trace<CfaState<?>, CfaAction> trace = (Trace<CfaState<?>, CfaAction>) safetyResult.asUnsafe()
							.getTrace();
					graph = TraceVisualizer.getDefault().visualize(CfaTraceConcretizer.concretize(trace));
				}
				final File tmpFile = File.createTempFile("theta", ".tmp");
				GraphvizWriter.getInstance().writeFile(graph, tmpFile.getAbsolutePath(), Format.SVG);
				final String image = Files.toString(tmpFile, Charsets.UTF_8);
				tmpFile.delete();
				Platform.runLater(() -> wvVisualResult.getEngine().loadContent(image));
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
		return "theta-cfa";
	}

	public static void main(final String args[]) {
		launch(args);
	}
}
