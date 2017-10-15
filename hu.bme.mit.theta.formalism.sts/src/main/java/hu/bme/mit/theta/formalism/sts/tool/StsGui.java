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
package hu.bme.mit.theta.formalism.sts.tool;

import java.io.File;
import java.util.Collection;

import com.google.common.base.Charsets;
import com.google.common.io.Files;

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.analysis.utils.TraceVisualizer;
import hu.bme.mit.theta.common.BaseGui;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.logging.impl.TextAreaLogger;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter.Format;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.StsUtils;
import hu.bme.mit.theta.formalism.sts.dsl.StsDslManager;
import hu.bme.mit.theta.formalism.sts.tool.StsConfigBuilder.Domain;
import hu.bme.mit.theta.formalism.sts.tool.StsConfigBuilder.InitPrec;
import hu.bme.mit.theta.formalism.sts.tool.StsConfigBuilder.PredSplit;
import hu.bme.mit.theta.formalism.sts.tool.StsConfigBuilder.Refinement;
import hu.bme.mit.theta.formalism.sts.tool.StsConfigBuilder.Search;
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
 * A graphical user interface for running a CEGAR configuration on an STS.
 */
public class StsGui extends BaseGui {
	private ChoiceBox<Domain> cbDomain;
	private ChoiceBox<Refinement> cbRefinement;
	private ChoiceBox<Search> cbSearch;
	private ChoiceBox<PredSplit> cbPredSplit;
	private ChoiceBox<InitPrec> cbInitPrec;
	private Spinner<Integer> spLogLevel;
	private Button btnRunAlgo;
	private Button btnLoadModel;
	private Button btnVisualizeResult;
	private CheckBox cbStructureOnly;

	private TextArea taModel;
	private TextArea taOutput;
	private WebView wvVisualResult;

	private Tab tabModel;
	private Tab tabOutput;
	private Tab tabVisualResult;

	private SafetyResult<?, ?> safetyResult;

	@Override
	protected void initializeControls(final Stage primaryStage) {
		taModel = new TextArea();
		taModel.setFont(Font.font("Consolas"));

		taOutput = new TextArea();
		taOutput.setEditable(false);

		wvVisualResult = new WebView();
		wvVisualResult.setOnScroll(
				evt -> wvVisualResult.setZoom((evt.getDeltaY() > 0 ? 1.1 : 1 / 1.1) * wvVisualResult.getZoom()));

		tabModel = createTab("Model Editor", taModel);
		tabOutput = createTab("Console Output", taOutput);
		tabVisualResult = createTab("Result Visualized", wvVisualResult);

		createTitle("Input model");
		btnLoadModel = createButton("Load STS");
		btnLoadModel.setOnMouseClicked(e -> btnLoadClicked(primaryStage));

		createTitle("Algorithm");
		cbDomain = createChoice("Domain", Domain.values());
		cbRefinement = createChoice("Refinement", Refinement.values());
		cbSearch = createChoice("Search", Search.values());
		cbPredSplit = createChoice("Predicate split", PredSplit.values());
		cbInitPrec = createChoice("Initial precision", InitPrec.values());
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
				final Collection<STS> stss = StsDslManager.createStsSpec(taModel.getText()).getAllSts();
				if (stss.size() != 1) {
					throw new UnsupportedOperationException("STS contains multiple properties.");
				}
				final STS sts = StsUtils.eliminateIte(Utils.singleElementOf(stss));
				final Config<?, ?, ?> config = new StsConfigBuilder(cbDomain.getValue(), cbRefinement.getValue())
						.search(cbSearch.getValue()).predSplit(cbPredSplit.getValue()).initPrec(cbInitPrec.getValue())
						.logger(new TextAreaLogger(spLogLevel.getValue(), taOutput)).build(sts);
				safetyResult = config.check();
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
		return "theta-sts";
	}

	public static void main(final String args[]) {
		launch(args);
	}
}
