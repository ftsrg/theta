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
package hu.bme.mit.theta.xta.tool;

import java.io.File;

import com.google.common.base.Charsets;
import com.google.common.io.Files;

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.SearchStrategy;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.analysis.utils.TraceVisualizer;
import hu.bme.mit.theta.common.BaseGui;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter.Format;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.XtaVisualizer;
import hu.bme.mit.theta.xta.analysis.lazy.Algorithm;
import hu.bme.mit.theta.xta.analysis.lazy.AlgorithmStrategy;
import hu.bme.mit.theta.xta.analysis.lazy.LazyXtaChecker;
import hu.bme.mit.theta.xta.analysis.lazy.LazyXtaStatistics;
import hu.bme.mit.theta.xta.dsl.XtaDslManager;
import javafx.application.Platform;
import javafx.concurrent.Task;
import javafx.scene.control.Button;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ChoiceBox;
import javafx.scene.control.Tab;
import javafx.scene.control.TextArea;
import javafx.scene.text.Font;
import javafx.scene.web.WebView;
import javafx.stage.FileChooser;
import javafx.stage.Stage;

public class XtaGui extends BaseGui {
	private ChoiceBox<Algorithm> cbAlgorithm;
	private ChoiceBox<SearchStrategy> cbSearchStrategy;
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
		final Button btnLoadModel = createButton("Load XTA");
		btnLoadModel.setOnMouseClicked(e -> btnLoadClicked(primaryStage));
		final Button btnVisualizeModel = createButton("Visualize XTA");
		btnVisualizeModel.setOnMouseClicked(e -> btnVisualizeModelClicked());

		createTitle("Algorithm");
		cbAlgorithm = createChoice("Algorithm", Algorithm.values());
		cbSearchStrategy = createChoice("Search", SearchStrategy.values());

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
				final XtaSystem system = XtaDslManager.createSystem(taModel.getText());
				final Algorithm algorithm = cbAlgorithm.getValue();
				final AlgorithmStrategy<?> algorithmStrategy = algorithm.createStrategy(system);
				final SearchStrategy searchStrategy = cbSearchStrategy.getValue();
				final LazyXtaChecker<?> checker = LazyXtaChecker.create(system, algorithmStrategy, searchStrategy);
				safetyResult = checker.check(UnitPrec.getInstance());
				final LazyXtaStatistics stats = (LazyXtaStatistics) safetyResult.getStats().get();
				Platform.runLater(() -> taOutput.setText(stats.toString()));
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
				final XtaSystem xta = XtaDslManager.createSystem(taModel.getText());
				final Graph graph = XtaVisualizer.visualize(xta);
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
				Graph graph = null;
				if (safetyResult.isSafe()) {
					if (cbStructureOnly.isSelected()) {
						graph = ArgVisualizer.getStructureOnly().visualize(safetyResult.asSafe().getArg());
					} else {
						graph = ArgVisualizer.getDefault().visualize(safetyResult.asSafe().getArg());
					}
				} else {
					graph = TraceVisualizer.getDefault().visualize(safetyResult.asUnsafe().getTrace());
				}
				final File tmpFile = File.createTempFile("theta", ".tmp");
				GraphvizWriter.getInstance().writeFile(graph, tmpFile.getAbsolutePath(), Format.SVG);
				final String image = Files.asCharSource(tmpFile, Charsets.UTF_8).read();
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
		return "theta-xta";
	}

	public static void main(final String args[]) {
		launch(args);
	}
}
