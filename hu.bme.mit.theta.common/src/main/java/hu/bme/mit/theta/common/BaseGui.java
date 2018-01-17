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
package hu.bme.mit.theta.common;

import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.List;
import java.util.function.Consumer;

import com.google.common.base.Charsets;
import com.google.common.io.Files;

import javafx.application.Application;
import javafx.application.Platform;
import javafx.concurrent.Task;
import javafx.geometry.Insets;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.control.Alert;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonType;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ChoiceBox;
import javafx.scene.control.Label;
import javafx.scene.control.Spinner;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import javafx.scene.control.TabPane.TabClosingPolicy;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.GridPane;
import javafx.scene.text.Text;
import javafx.stage.Stage;

/**
 * Base class for tool GUIs.
 */
public abstract class BaseGui extends Application {
	private GridPane controls;
	private int nRows = 0;

	private TabPane tabPane;

	@Override
	public void start(final Stage primaryStage) throws Exception {
		primaryStage.setMinHeight(400);
		primaryStage.setMinWidth(600);
		final BorderPane mainPane = new BorderPane();

		tabPane = new TabPane();
		tabPane.setTabClosingPolicy(TabClosingPolicy.UNAVAILABLE);

		controls = new GridPane();

		mainPane.setLeft(controls);
		mainPane.setCenter(tabPane);

		initializeControls(primaryStage);

		final Scene scene = new Scene(mainPane);
		primaryStage.setTitle(getTitle());
		primaryStage.setScene(scene);
		primaryStage.show();
	}

	protected abstract void initializeControls(final Stage primaryStage);

	protected abstract String getTitle();

	protected Button createButton(final String label) {
		final Button btn = new Button(label);
		btn.setMaxSize(Double.MAX_VALUE, Double.MAX_VALUE);
		GridPane.setFillWidth(btn, true);
		controls.add(btn, 0, nRows, 2, 1);
		nRows++;
		return btn;
	}

	protected <T> ChoiceBox<T> createChoice(final String label, final T[] choices) {
		return createChoice(label, Arrays.asList(choices));
	}

	protected <T> ChoiceBox<T> createChoice(final String label, final List<T> choices) {
		final ChoiceBox<T> cb = new ChoiceBox<>();
		cb.getItems().setAll(choices);
		cb.getSelectionModel().selectFirst();
		cb.setMaxSize(Double.MAX_VALUE, Double.MAX_VALUE);
		GridPane.setFillWidth(cb, true);
		controls.add(new Text(label + ":"), 0, nRows);
		controls.add(cb, 1, nRows);
		nRows++;
		return cb;
	}

	protected Spinner<Integer> createSpinner(final String label, final int min, final int max, final int init) {
		final Spinner<Integer> sp = new Spinner<>(min, max, init);
		sp.setMaxSize(Double.MAX_VALUE, Double.MAX_VALUE);
		GridPane.setFillWidth(sp, true);
		controls.add(new Text(label + ":"), 0, nRows);
		controls.add(sp, 1, nRows);
		nRows++;
		return sp;
	}

	protected CheckBox createCheckBox(final String label) {
		final CheckBox cb = new CheckBox(label);
		controls.add(cb, 0, nRows, 2, 1);
		nRows++;
		return cb;
	}

	protected Tab createTab(final String text, final Node content) {
		final Tab tab = new Tab(text, content);
		tabPane.getTabs().add(tab);
		return tab;
	}

	protected void createTitle(final String label) {
		final Label txt = new Label(label);
		txt.setStyle("-fx-font-size: 20px");
		if (nRows != 0) {
			txt.setPadding(new Insets(10, 0, 0, 0));
		}
		controls.add(txt, 0, nRows, 2, 1);
		nRows++;
	}

	protected static void displayException(final Exception ex) {
		final Alert alert = new Alert(AlertType.ERROR, ex.getMessage(), ButtonType.OK);
		alert.setHeaderText("Exception type: " + ex.getClass().getSimpleName());
		alert.setTitle("Error");
		alert.showAndWait();
	}

	protected void disableControls(final boolean disabled) {
		controls.setDisable(disabled);
	}

	protected void selectTab(final Tab tab) {
		tabPane.getSelectionModel().select(tab);
	}

	protected void runBackgroundTask(final Task<?> task) {
		disableControls(true);
		final Thread th = new Thread(task);
		th.setDaemon(true);
		th.start();
	}

	protected final class LoadFileTextTask extends Task<Void> {
		private final String path;
		private final Consumer<String> callback;

		public LoadFileTextTask(final String path, final Consumer<String> callback) {
			this.path = path;
			this.callback = callback;
		}

		@Override
		protected Void call() throws Exception {
			String text = "";
			try {
				text = Files.asCharSource(new File(path), Charsets.UTF_8).read();
			} catch (final IOException ex) {
				Platform.runLater(() -> displayException(ex));
				text = "";
			} finally {
				final String finalText = text;
				Platform.runLater(() -> callback.accept(finalText));
				Platform.runLater(() -> disableControls(false));
			}
			return null;
		}
	}
}
