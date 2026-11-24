/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.zip.ZipFile;
import javafx.collections.FXCollections;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.ListCell;
import javafx.scene.control.ListView;
import javafx.scene.control.SelectionMode;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.Region;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.Window;

import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF.Kind;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This dialog allows the user to select the proof to load from a proof bundle ({@code .zproof}
 * zip archive). Counter-part of {@code de.uka.ilkd.key.gui.ProofSelectionDialog} in the Swing
 * module {@code key.ui}: it lists all {@code .proof} files on the top level of the bundle (with
 * contract-style proof names abbreviated) and returns the chosen entry relative to the bundle
 * root. The bundle reading on load is provided by key.core ({@code AbstractProblemLoader} unzips
 * the bundle and loads the chosen proof file).
 *
 * @author Wolfram Pfeifer (original Swing dialog)
 */
public final class ProofSelectionDialogF {

    private static final Logger LOGGER = LoggerFactory.getLogger(ProofSelectionDialogF.class);

    /**
     * Regex for identifiers (class, method), which catches for example "java.lang.Object",
     * "SumAndMax", "sort(int[] a)", ...
     */
    private static final String IDENT = "(.*)";

    /**
     * Regex for the type of the contract (catches something like "JML normal_behavior operation
     * contract").
     */
    private static final String TYPE = "(.*)";

    /**
     * Regex for the number of the proof.
     */
    private static final String NUM = "(\\d+)";

    /**
     * The pattern to match the filename of the proof.
     */
    private static final Pattern PROOF_NAME_PATTERN = Pattern.compile(
        IDENT + "\\(" + IDENT + "__" + IDENT + "\\)\\)\\." + TYPE + "." + NUM + ".proof");

    /**
     * The path of the proof to load (relative to the root of the proof bundle, so actually just
     * the filename of the proof file inside the bundle).
     */
    private @Nullable Path proofToLoad;

    private final Stage stage = new Stage();

    /**
     * Creates a new ProofSelectionDialog for the given proof
     *
     * @param bundlePath the path of the proof bundle to load
     * @param owner the owner window of the modal dialog
     * @throws IOException if the proof bundle can not be read
     */
    private ProofSelectionDialogF(Path bundlePath, @Nullable Window owner) throws IOException {
        stage.setTitle("Choose proof to load");

        // create and fill list with proofs available for loading
        ListView<Path> list = createAndFillList(bundlePath);

        // create scroll pane with list ("Proofs found in bundle:" — Swing TitledBorder)
        Label heading = new Label("Proofs found in bundle:");
        heading.getStyleClass().add("dialog-section-title");
        BorderPane.setMargin(heading, new Insets(4, 8, 4, 8));
        BorderPane content = new BorderPane(list, heading, null, null, null);
        BorderPane.setMargin(list, new Insets(0, 8, 0, 8));

        // create panel with buttons
        Button okButton = new Button("OK");
        okButton.setDefaultButton(true);
        okButton.setOnAction(e -> {
            proofToLoad = list.getSelectionModel().getSelectedItem();
            stage.close();
        });
        // disable "Ok" button if no proof was found
        okButton.setDisable(list.getItems().isEmpty());
        Button cancelButton = new Button("Cancel");
        cancelButton.setCancelButton(true);
        cancelButton.setOnAction(e -> stage.close());
        Region spacer = new Region();
        HBox.setHgrow(spacer, Priority.ALWAYS);
        HBox buttonPanel = new HBox(5, spacer, okButton, cancelButton);
        buttonPanel.setAlignment(Pos.CENTER_RIGHT);
        buttonPanel.setPadding(new Insets(5, 8, 8, 8));
        content.setBottom(buttonPanel);

        stage.initModality(Modality.WINDOW_MODAL);
        if (owner != null) {
            stage.initOwner(owner);
        }
        Scene scene = new Scene(content, 450, 300);
        ThemeManager.getInstance().style(scene);
        stage.setScene(scene);
    }

    /**
     * Creates a ListView and fills it with the proofs found in the bundle.
     *
     * @param bundlePath the path of the proof bundle
     * @return the created list
     * @throws IOException if the proof bundle can not be read
     */
    private ListView<Path> createAndFillList(Path bundlePath) throws IOException {
        // create a list of all *.proof files (only top level in bundle)
        List<Path> proofs;
        // read zip
        try (ZipFile bundle = new ZipFile(bundlePath.toFile())) {
            proofs = bundle.stream().filter(e -> !e.isDirectory())
                    .filter(e -> e.getName().endsWith(".proof")).map(e -> Paths.get(e.getName()))
                    .collect(Collectors.toList());
        }

        // show the list in a ListView
        ListView<Path> list = new ListView<>(FXCollections.observableArrayList(proofs));
        list.getSelectionModel().setSelectionMode(SelectionMode.SINGLE);
        list.getSelectionModel().selectFirst();
        list.setCellFactory(view -> new ListCell<>() {
            @Override
            protected void updateItem(Path item, boolean empty) {
                super.updateItem(item, empty);
                // cells are reused: reset the text on every update
                setText(empty || item == null ? null : abbreviateProofPath(item));
            }
        });
        list.setOnMouseClicked(e -> {
            // double click chooses the proof (Swing: mouse listener with getClickCount() >= 2)
            if (e.getClickCount() >= 2) {
                proofToLoad = list.getSelectionModel().getSelectedItem();
                stage.close();
            }
        });
        return list;
    }

    /**
     * Abbreviates the filename of the proof if it matches the usual KeY format.
     *
     * @param proofPath the path (actually only the filename) of the proof
     * @return the abbreviated proof name if it matches, the given path as String otherwise
     */
    private static String abbreviateProofPath(Path proofPath) {

        final String pathString = proofPath.toString();
        Matcher m = PROOF_NAME_PATTERN.matcher(pathString);
        if (m.matches() && m.groupCount() == 5) {
            String className = m.group(1);
            String method = m.group(3);
            String type = m.group(4).toLowerCase();
            String num = m.group(5);

            // type is either "normal", "exceptional", or empty
            if (type.contains("normal")) {
                type = "normal ";
            } else if (type.contains("exceptional")) {
                type = "exceptional ";
            } else {
                type = "";
            }

            // the stray closing parenthesis is part of the Swing original's output
            return className + "::" + method + ") " + type + num;
        }
        // fallback: use complete filename
        return pathString;
    }

    /**
     * Shows the dialog with the given path and returns the filename of the proof to load.
     *
     * @param bundlePath the path of the proof bundle
     * @param owner the owner window of the modal dialog
     * @return the filename of the proof to load
     */
    private static @Nullable Path showDialog(Path bundlePath, @Nullable Window owner) {
        Path proofPath = null;
        try {
            ProofSelectionDialogF dialog = new ProofSelectionDialogF(bundlePath, owner);
            dialog.stage.showAndWait();
            proofPath = dialog.proofToLoad;
        } catch (IOException exc) {
            LOGGER.error("", exc);
            // Swing: IssueDialog.showExceptionDialog; the JavaFX UI reports via error toast
            NotificationManagerF.getInstance()
                    .notify("Could not read the proof bundle " + bundlePath + ": "
                        + exc.getMessage(), Kind.ERROR);
        }
        return proofPath;
    }

    /**
     * Shows a dialog and allows the user to choose the proof to load from a bundle.
     *
     * @param bundlePath the path of the proof bundle that is loaded
     * @param owner the owner window of the modal dialog (the main window stage)
     * @return the path of the proof relative to the bundle (proofs are always top level, which
     *         means the returned path will only contains the filename of the proof file) or null
     *         if the given path does not denote a bundle
     */
    public static @Nullable Path chooseProofToLoad(Path bundlePath, @Nullable Window owner) {
        if (isProofBundle(bundlePath)) {
            return showDialog(bundlePath, owner);
        }
        return null;
    }

    /**
     * Checks if a path denotes a proof bundle.
     *
     * @param path the path to check
     * @return true iff the path denotes a proof bundle
     */
    public static boolean isProofBundle(Path path) {
        return path.toString().endsWith(".zproof");
    }
}
