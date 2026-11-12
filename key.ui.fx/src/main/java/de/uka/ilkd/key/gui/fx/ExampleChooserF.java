/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.control.Alert;
import javafx.scene.control.Button;
import javafx.scene.control.CheckBox;
import javafx.scene.control.Label;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.SelectionMode;
import javafx.scene.control.SplitPane;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import javafx.scene.control.TextArea;
import javafx.scene.control.TreeCell;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;
import javafx.scene.input.KeyCode;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.Region;
import javafx.scene.layout.VBox;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.Window;

import de.uka.ilkd.key.gui.fx.configuration.ConfigF;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

import org.key_project.util.java.IOUtil;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Dialog to choose an example to load. Counter-part of {@code de.uka.ilkd.key.gui.ExampleChooser}
 * in the Swing module {@code key.ui}: a category tree of the examples on the left and a tabbed
 * preview (description, proof obligation, additional files) on the right, with "Load Example",
 * "Load Proof" and "Cancel" buttons plus the "show on startup" checkbox (the checkbox state is
 * shared with the Swing UI via the core {@link ViewSettings}).
 * <p>
 * Deviations from the Swing original: the dialog is built fresh on every invocation (Swing caches
 * a singleton instance and would keep a stale example list if the examples directory changed),
 * and an empty example list leaves the buttons disabled instead of enabled.
 */
public final class ExampleChooserF {

    /**
     * This path is also accessed by the Eclipse integration of KeY to find the right examples.
     */
    public static final String EXAMPLES_PATH = "examples";

    /**
     * Java property name to specify a custom key example folder.
     */
    public static final String KEY_EXAMPLE_DIR = "key.examples.dir";

    private static final Logger LOGGER = LoggerFactory.getLogger(ExampleChooserF.class);

    /** The result value of the dialog. {@code null} if nothing to be loaded */
    private @Nullable Path fileToLoad = null;

    /** The currently selected example. {@code null} if none selected */
    private @Nullable ExampleF selectedExample;

    private final Stage stage = new Stage();
    private final TreeView<Object> exampleList = new TreeView<>();
    private final TabPane tabPane = new TabPane();
    private final Button loadButton = new Button("Load Example");
    private final Button loadProofButton = new Button("Load Proof");
    private final Button cancelButton = new Button("Cancel");

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    private ExampleChooserF(Path examplesDir, @Nullable Window owner) {
        assert examplesDir != null;

        // create example list: category folders with one leaf per example (Swing JTree)
        List<ExampleF> examples = listExamples(examplesDir);
        TreeItem<Object> root = new TreeItem<>(null);
        for (ExampleF example : examples) {
            findChild(root, example.getPath(), 0).getChildren().add(new TreeItem<>(example));
        }
        exampleList.setRoot(root);
        exampleList.setShowRoot(false);
        exampleList.getSelectionModel().setSelectionMode(SelectionMode.SINGLE);
        exampleList.getSelectionModel().selectedItemProperty()
                .addListener((obs, old, item) -> updateDescription());
        exampleList.setCellFactory(view -> new TreeCell<>() {
            {
                setOnMouseClicked(e -> {
                    // double click on an example loads it (Swing: loadButton.doClick())
                    if (e.getClickCount() == 2 && !isEmpty() && getItem() instanceof ExampleF) {
                        doLoadExample();
                    }
                });
            }

            @Override
            protected void updateItem(Object item, boolean empty) {
                super.updateItem(item, empty);
                // cells are reused: reset the text on every update
                setText(empty || item == null ? null
                        : item instanceof ExampleF example ? example.getName()
                                : (String) item);
            }
        });

        ScrollPane exampleScrollPane = new ScrollPane(exampleList);
        exampleScrollPane.setFitToWidth(true);
        VBox exampleSection = titled("Examples", exampleScrollPane);
        VBox.setVgrow(exampleScrollPane, Priority.ALWAYS);

        // create description label (Swing JTabbedPane)
        VBox tabSection = new VBox();
        tabSection.getChildren().add(tabPane);
        VBox.setVgrow(tabPane, Priority.ALWAYS);

        SplitPane split = new SplitPane(exampleSection, tabSection);
        split.setDividerPositions(300.0 / 800);

        // create the checkbox to hide example load on next startup (shared core setting)
        ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        CheckBox showAgainCheckbox = new CheckBox("Show this dialog on startup");
        showAgainCheckbox.setSelected(vs.getShowLoadExamplesDialog());
        showAgainCheckbox.selectedProperty()
                .addListener((obs, old, selected) -> vs.setShowLoadExamplesDialog(selected));

        // create "load" button
        loadButton.setDefaultButton(true);
        loadButton.setDisable(true);
        loadButton.setOnAction(e -> doLoadExample());

        // create "load proof" button
        loadProofButton.setDisable(true);
        loadProofButton.setOnAction(e -> doLoadProof());

        // create "cancel" button
        cancelButton.setCancelButton(true);
        cancelButton.setOnAction(e -> doCancel());

        HBox buttonPanel = new HBox(5);
        buttonPanel.setAlignment(Pos.CENTER_RIGHT);
        buttonPanel.setPadding(new Insets(5));
        Region spacer = new Region();
        HBox.setHgrow(spacer, Priority.ALWAYS);
        buttonPanel.getChildren().addAll(showAgainCheckbox, spacer, loadButton, loadProofButton,
            cancelButton);

        BorderPane rootPane = new BorderPane();
        rootPane.setCenter(split);
        rootPane.setBottom(buttonPanel);

        stage.setTitle("Load Example");
        if (owner != null) {
            stage.initOwner(owner);
            stage.initModality(Modality.WINDOW_MODAL);
        }
        Scene scene = new Scene(rootPane, 800, 400);
        ThemeManager.getInstance().style(scene);
        stage.setScene(scene);
        // Swing GuiUtilities.attachClickOnEscListener(cancelButton)
        scene.setOnKeyPressed(e -> {
            if (e.getCode() == KeyCode.ESCAPE) {
                doCancel();
            }
        });

        // select the first example (Swing: select and make visible the first leaf)
        TreeItem<Object> firstLeaf = firstLeaf(root);
        if (firstLeaf != null) {
            for (TreeItem<Object> item = firstLeaf; item != null; item = item.getParent()) {
                item.setExpanded(true);
            }
            exampleList.getSelectionModel().select(firstLeaf);
        }
    }

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    /**
     * Wraps the given content in a section with a title label (the Swing original uses
     * {@code TitledBorder}).
     */
    private static VBox titled(String title, Node content) {
        Label heading = new Label(title);
        heading.getStyleClass().add("dialog-section-title");
        VBox box = new VBox(heading, content);
        VBox.setVgrow(content, Priority.ALWAYS);
        return box;
    }

    public static Path lookForExamples() {
        // weigl: using java properties: -Dkey.examples.dir="..."
        if (System.getProperty(KEY_EXAMPLE_DIR) != null) {
            return Paths.get(System.getProperty(KEY_EXAMPLE_DIR));
        }

        // greatly simplified version without parent path lookup.
        File projectRoot = IOUtil.getProjectRoot(ExampleChooserF.class);
        File folder = projectRoot != null ? new File(projectRoot, EXAMPLES_PATH)
                : new File(EXAMPLES_PATH);
        if (!folder.exists()) {
            File classLocation = IOUtil.getClassLocation(ExampleChooserF.class);
            folder = classLocation != null ? new File(classLocation, EXAMPLES_PATH)
                    : new File(EXAMPLES_PATH);
        }
        return folder.toPath();
    }

    private static String fileAsString(Path f) {
        try {
            return Files.readString(f);
        } catch (IOException e) {
            LOGGER.error("Could not read file '{}'", f, e);
            return "<Error reading file: " + f + ">";
        }
    }

    private void updateDescription() {
        TreeItem<Object> item = exampleList.getSelectionModel().getSelectedItem();
        if (item == null) {
            return;
        }

        tabPane.getTabs().clear();

        if (item.getValue() instanceof ExampleF example) {
            if (example != selectedExample) {
                addTab(example.getDescription(), "Description", true);
                final String fileAsString = fileAsString(example.getObligationFile());
                final int p = fileAsString.lastIndexOf("\\problem");
                if (p >= 0) {
                    addTab(fileAsString.substring(p), "Proof Obligation", false);
                }
                for (Path file : example.getAdditionalFiles()) {
                    addTab(fileAsString(file), file.getFileName().toString(), false);
                }
                loadButton.setDisable(false);
                loadProofButton.setDisable(!example.hasProof());
                selectedExample = example;
            }
        } else {
            selectedExample = null;
            loadButton.setDisable(true);
            loadProofButton.setDisable(true);
        }
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    private void addTab(String string, String name, boolean wrap) {
        TextArea area = new TextArea(string);
        area.setFont(ConfigF.DEFAULT.monoFont());
        area.setEditable(false);
        area.setWrapText(wrap);
        Tab tab = new Tab(name, area);
        tab.setClosable(false);
        tabPane.getTabs().add(tab);
    }

    /**
     * Shows the dialog (modal to the given owner), using the passed examples directory. If
     * {@code null} is passed, tries to find the examples directory on its own.
     *
     * @param examplesDirString the examples directory, or {@code null} to look it up
     * @param owner the owner window of the modal dialog (the main window stage)
     * @return the file to load, or {@code null} if the dialog was canceled or no examples
     *         directory could be found
     */
    public static @Nullable Path showInstance(@Nullable Path examplesDirString,
            @Nullable Window owner) {
        // get examples directory
        Path examplesDir;
        if (examplesDirString == null) {
            examplesDir = lookForExamples();
        } else {
            examplesDir = examplesDirString;
        }

        if (!Files.isDirectory(examplesDir)) {
            Alert alert = new Alert(Alert.AlertType.ERROR);
            alert.setTitle("Error loading examples");
            alert.setHeaderText(null);
            alert.setContentText("The examples directory cannot be found.\n"
                + "Please install them at "
                + (examplesDirString == null
                        ? IOUtil.getProjectRoot(ExampleChooserF.class) + "/"
                        : examplesDirString));
            themeDialogPane(alert);
            alert.showAndWait();
            return null;
        }

        // show dialog (a fresh dialog is built on every invocation — see class comment)
        ExampleChooserF instance = new ExampleChooserF(examplesDir, owner);
        instance.stage.showAndWait();

        // return result
        return instance.fileToLoad;
    }

    /**
     * Applies the current theme stylesheet to the content pane of an {@link Alert} (its scene
     * only exists while it is shown, so the pane itself is styled — {@code Parent} stylesheets
     * combine with the scene's).
     */
    static void themeDialogPane(Alert alert) {
        alert.getDialogPane()
                .getStylesheets()
                .add(ThemeManager.getInstance().getTheme().stylesheetUrl());
    }

    /**
     * Lists all examples in the given directory. This method is also accessed by the eclipse
     * based projects.
     *
     * @param examplesDir The examples directory to list examples in.
     * @return The found examples.
     */
    public static List<ExampleF> listExamples(Path examplesDir) {
        List<ExampleF> result = new ArrayList<>(64);

        final Path index = examplesDir.resolve("index").resolve("samplesIndex.txt");
        try {
            for (var line : Files.readAllLines(index)) {
                line = line.trim();
                if (line.startsWith("#") || line.isEmpty()) {
                    continue;
                }
                Path f = examplesDir.resolve(line);
                try {
                    result.add(new ExampleF(f));
                } catch (IOException e) {
                    LOGGER.warn("Cannot parse example {}; ignoring it.", f, e);
                }
            }
        } catch (IOException e) {
            LOGGER.warn("Error while reading samples", e);
        }
        return result;
    }

    /** The "Load Example" button: loads the example's obligation file. */
    private void doLoadExample() {
        if (selectedExample == null) {
            // unreachable: the button is disabled without a selection (Swing throws here)
            LOGGER.info("No example selected");
            return;
        }
        fileToLoad = selectedExample.getObligationFile();
        stage.close();
    }

    /** The "Load Proof" button: loads the example's saved proof file. */
    private void doLoadProof() {
        if (selectedExample == null || !selectedExample.hasProof()) {
            // unreachable: the button is disabled unless the example has a proof
            LOGGER.info("Selected example has no proof.");
            return;
        }
        fileToLoad = selectedExample.getProofFile();
        stage.close();
    }

    private void doCancel() {
        fileToLoad = null;
        stage.close();
    }

    /**
     * Finds (or creates) the category folder for the given path segments (Swing
     * {@code Example.findChild} over tree items).
     */
    private static TreeItem<Object> findChild(TreeItem<Object> root, String[] path, int from) {
        if (from == path.length) {
            return root;
        }
        for (TreeItem<Object> node : root.getChildren()) {
            if (path[from].equals(node.getValue())) {
                return findChild(node, path, from + 1);
            }
        }
        // not found ==> add new
        TreeItem<Object> node = new TreeItem<>(path[from]);
        root.getChildren().add(node);
        return findChild(node, path, from + 1);
    }

    /**
     * @return the first leaf of the tree (the first example), or {@code null} if the tree is empty
     */
    private static @Nullable TreeItem<Object> firstLeaf(TreeItem<Object> node) {
        if (node.getChildren().isEmpty()) {
            return node.getValue() instanceof ExampleF ? node : null;
        }
        return firstLeaf(node.getChildren().get(0));
    }
}
