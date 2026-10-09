/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.settings;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import javafx.geometry.Insets;
import javafx.scene.Scene;
import javafx.scene.control.Alert;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonBar;
import javafx.scene.control.Label;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.TextField;
import javafx.scene.control.TreeCell;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;
import javafx.scene.image.Image;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.StackPane;
import javafx.scene.layout.VBox;
import javafx.stage.Modality;
import javafx.stage.Stage;

import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.plugins.javac.JavacSettingsProviderF;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Aggregates the registered {@link SettingsProviderF}s and opens the settings dialog.
 * Counter-part of the Swing classes {@code SettingsManager}, {@code SettingsDialog} and
 * {@code SettingsUi} of the module {@code key.ui} (the Swing originals are three classes; they
 * are merged here like the other close Swing pairs in this module).
 * <p>
 * The dialog is built in code (no FXML): a tree of providers on the left (root entry "KeY
 * Settings", providers and their {@link SettingsProviderF#getChildProviders() children}), the
 * selected
 * provider's panel on the right, and OK / Apply / Cancel controls with the Swing semantics:
 * <ul>
 * <li><b>OK</b> applies every provider; on errors the errors are shown and the dialog stays
 * open, otherwise it closes,</li>
 * <li><b>Apply</b> applies every provider and shows occurring errors, staying open,</li>
 * <li><b>Cancel</b> closes the dialog without applying; {@code Escape} is the cancel key.</li>
 * </ul>
 * Providers are sorted by {@link SettingsProviderF#getPriorityOfSettings()} (higher values last)
 * and initialized ({@code getPanel}) before the dialog is shown, like the Swing
 * {@code initializeProviders}.
 */
public final class SettingsManagerF {

    private static final Logger LOGGER = LoggerFactory.getLogger(SettingsManagerF.class);

    /** the first provider of the tree (Swing {@code SettingsManager.STANDARD_UI_SETTINGS}) */
    public static final StandardUISettingsF STANDARD_UI_SETTINGS = new StandardUISettingsF();

    /** the taclet options provider (Swing {@code SettingsManager.TACLET_OPTIONS_SETTINGS}) */
    public static final TacletOptionsSettingsF TACLET_OPTIONS_SETTINGS =
        new TacletOptionsSettingsF();

    /**
     * smalldialogs: the javac options provider (Swing {@code JavacSettingsProvider}, the
     * settings tab of the {@code JavacExtension} plugin). Swing reaches it via the
     * {@code KeYGuiExtension.Settings} capability; the FX extension SPI does not exist yet, so
     * it is registered directly here (the provider seam stays open for the SPI).
     */
    public static final JavacSettingsProviderF JAVAC_SETTINGS =
        new JavacSettingsProviderF();

    /**
     * menu: MP4 — the SMT options provider (Swing {@code SMTSettingsProvider}, registered as
     * {@code SettingsManager.SMT_SETTINGS} between the standard UI and the taclet options,
     * SettingsManager.java:37-63); the target of the Options | SMT Solvers… action
     * (Swing {@code SMTOptionsAction}).
     */
    public static final SMTSettingsProviderF SMT_SETTINGS = new SMTSettingsProviderF();

    // Deliberately deferred to later milestones (the provider seam stays open):
    // ParallelProverSettingsProvider, FeatureSettingsPanel and the ShowActiveSettings dump.

    private static SettingsManagerF INSTANCE;

    private final List<SettingsProviderF> settingsProviders = new ArrayList<>();

    private SettingsManagerF() {
    }

    /**
     * @return the global settings manager instance with the built-in providers registered
     */
    public static SettingsManagerF getInstance() {
        if (INSTANCE == null) {
            INSTANCE = new SettingsManagerF();
            INSTANCE.add(STANDARD_UI_SETTINGS);
            // menu: MP4 — SMT between the standard UI and the taclet options, like the Swing
            // SettingsManager registration order (SettingsManager.java:59-63)
            INSTANCE.add(SMT_SETTINGS);
            INSTANCE.add(TACLET_OPTIONS_SETTINGS);
            INSTANCE.add(JAVAC_SETTINGS);
        }
        return INSTANCE;
    }

    /**
     * The choice settings of the given window: a detached copy initialized from the selected
     * proof (its default choices and categories) if a proof is loaded, otherwise the global
     * default settings (Swing {@code SettingsManager.getChoiceSettings}).
     *
     * @param window the main window
     * @return the choice settings to edit in the taclet options panel
     */
    public static ChoiceSettings getChoiceSettings(MainWindowF window) {
        Proof selectedProof = window.getMediator().getSelectedProof();
        if (selectedProof != null) {
            ChoiceSettings settings = new ChoiceSettings();
            settings.setDefaultChoices(
                selectedProof.getSettings().getChoiceSettings().getDefaultChoices());
            var cat = selectedProof.getSettings().getChoiceSettings().getCategory2Choices();
            if (cat.isEmpty()) {
                cat = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getCategory2Choices();
            }
            settings.setChoiceCategories(new java.util.TreeMap<>(cat));
            return settings;
        }
        return ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
    }

    /**
     * Registers a settings provider.
     *
     * @param settingsProvider the provider to register
     * @return whether the provider was added
     */
    public boolean add(SettingsProviderF settingsProvider) {
        return settingsProviders.add(settingsProvider);
    }

    /**
     * Removes the given settings provider.
     *
     * @param settingsProvider the provider to remove
     * @return whether the provider was removed
     */
    public boolean remove(SettingsProviderF settingsProvider) {
        return settingsProviders.remove(settingsProvider);
    }

    /**
     * Opens the settings dialog, modal to the main window (Swing
     * {@code SettingsManager.showSettingsDialog}).
     *
     * @param mainWindow the main window
     */
    public void showSettingsDialog(MainWindowF mainWindow) {
        Stage dialog = createDialog(mainWindow);
        dialog.show();
    }

    /**
     * Opens the settings dialog with the given provider selected in the tree (Swing
     * {@code showSettingsDialog(MainWindow, SettingsProvider)}).
     *
     * @param mainWindow the main window
     * @param selectedPanel the provider to select
     */
    public void showSettingsDialog(MainWindowF mainWindow, SettingsProviderF selectedPanel) {
        Stage dialog = createDialog(mainWindow);
        ((SettingsUi) dialog.getUserData()).selectPanel(selectedPanel);
        dialog.show();
    }

    private Stage createDialog(MainWindowF mainWindow) {
        List<SettingsProviderF> providers = new ArrayList<>(settingsProviders);
        providers.sort(Comparator.comparingInt(SettingsProviderF::getPriorityOfSettings));
        initializeProviders(providers, mainWindow);

        Stage stage = new Stage();
        stage.initOwner(mainWindow.getStage());
        stage.initModality(Modality.APPLICATION_MODAL);
        stage.setTitle("Settings");
        Image logo = new Image(getClass()
                .getResourceAsStream("/de/uka/ilkd/key/gui/images/key-color-icon-square.png"));
        if (!logo.isError()) {
            stage.getIcons().add(logo);
        }

        SettingsUi ui = new SettingsUi(mainWindow, providers);
        BorderPane root = new BorderPane(ui);
        root.setPadding(new Insets(8));
        root.setBottom(createButtonBar(mainWindow, providers, stage));
        stage.setScene(new Scene(root, 900, 600));
        // track the dialog scene so it is styled with the current theme and follows theme
        // switches applied by its own appearance panel while it is open
        ThemeManager.getInstance().manage(stage.getScene());
        stage.setUserData(ui);

        stage.getScene().addEventFilter(javafx.scene.input.KeyEvent.KEY_PRESSED, e -> {
            // Swing registers ESCAPE on the root pane (WHEN_IN_FOCUSED_WINDOW): Escape closes
            // the dialog from any focus. The event filter catches the key before controls like
            // the provider tree consume it; an open cell editor still wins (its Escape cancels
            // the edit), like the WHEN_ANCESTOR bindings of the Swing cell editors.
            if (e.getCode() == javafx.scene.input.KeyCode.ESCAPE
                    && !isCellEditing(stage.getScene().getFocusOwner())) {
                stage.close();
                e.consume();
            }
        });
        return stage;
    }

    /**
     * @return whether the focus owner or one of its ancestors is an editing cell, so the Escape
     *         key belongs to the cell editor and must not close the dialog
     */
    private static boolean isCellEditing(javafx.scene.Node node) {
        while (node != null) {
            if (node instanceof javafx.scene.control.IndexedCell<?> cell && cell.isEditing()) {
                return true;
            }
            node = node.getParent();
        }
        return false;
    }

    private javafx.scene.Node createButtonBar(MainWindowF mainWindow,
            List<SettingsProviderF> providers, Stage stage) {
        ButtonBar bar = new ButtonBar();
        Button acceptButton = new Button("OK");
        Button applyButton = new Button("Apply");
        Button cancelButton = new Button("Cancel");
        ButtonBar.setButtonData(acceptButton, ButtonBar.ButtonData.OK_DONE);
        ButtonBar.setButtonData(applyButton, ButtonBar.ButtonData.APPLY);
        ButtonBar.setButtonData(cancelButton, ButtonBar.ButtonData.CANCEL_CLOSE);
        cancelButton.setOnAction(e -> stage.close()); // Swing CancelAction: setVisible(false)
        acceptButton.setOnAction(e -> { // Swing AcceptAction: setVisible(!showErrors(apply()))
            if (showErrors(apply(providers, mainWindow), stage)) {
                stage.close();
            }
        });
        applyButton.setOnAction(e -> showErrors(apply(providers, mainWindow), stage));
        bar.getButtons().addAll(acceptButton, applyButton, cancelButton);
        return bar;
    }

    /**
     * Applies all registered providers recursively, collecting the thrown exceptions (Swing
     * {@code SettingsDialog.apply}).
     *
     * @param providers the providers to apply
     * @param mainWindow the main window
     * @return the collected errors, empty on success
     */
    private List<Exception> apply(List<SettingsProviderF> providers, MainWindowF mainWindow) {
        List<Exception> exceptions = new LinkedList<>();
        apply(providers, mainWindow, exceptions);
        return exceptions;
    }

    private void apply(List<SettingsProviderF> providers, MainWindowF mainWindow,
            List<Exception> exceptions) {
        for (SettingsProviderF it : providers) {
            try {
                it.apply(mainWindow);
                apply(it.getChildProviders(), mainWindow, exceptions);
            } catch (Exception e) {
                exceptions.add(e);
            }
        }
    }

    /**
     * Shows the collected errors in a dialog and logs them (Swing
     * {@code SettingsDialog.showErrors}).
     *
     * @param exceptions the errors
     * @param owner the owner window
     * @return true iff there were no errors
     */
    private boolean showErrors(List<Exception> exceptions, javafx.stage.Window owner) {
        if (exceptions.isEmpty()) {
            return true;
        }
        for (Exception e : exceptions) {
            LOGGER.error("", e);
        }
        String msg = exceptions.stream().map(Throwable::getMessage).collect(Collectors
                .joining("\n"));
        Alert alert = new Alert(Alert.AlertType.ERROR, msg);
        alert.setTitle("Error in Settings");
        alert.setHeaderText("Error in Settings");
        if (owner != null) {
            alert.initOwner(owner);
        }
        alert.showAndWait();
        return false;
    }

    /**
     * Ensures that every given setting provider can update its model based on the current main
     * window, including the children (Swing {@code SettingsManager.initializeProviders}).
     */
    private void initializeProviders(List<SettingsProviderF> providers, MainWindowF mainWindow) {
        providers.forEach(it -> it.getPanel(mainWindow));
        providers.forEach(it -> initializeProviders(it.getChildProviders(), mainWindow));
    }

    /**
     * The content of the settings dialog: the provider tree with a search field on the left and
     * the selected panel on the right (Swing {@code SettingsUi}).
     */
    private static class SettingsUi extends BorderPane {

        private final MainWindowF mainWindow;
        private final TreeView<SettingsProviderF> treeSettingsPanels = new TreeView<>();
        private final TextField txtSearch = new TextField();
        private final Map<TreeItem<SettingsProviderF>, SettingsProviderF> providerByItem =
            new IdentityHashMap<>();
        private final ScrollPane panelArea = new ScrollPane();
        private final StackPane panelHolder = new StackPane();

        SettingsUi(MainWindowF mainWindow, List<SettingsProviderF> providers) {
            this.mainWindow = mainWindow;

            txtSearch.setPromptText("Search");
            txtSearch.textProperty()
                    .addListener((obs, old, value) -> treeSettingsPanels.refresh());

            // the placeholder must be in place before buildTree shows the first panel
            panelArea.setContent(panelHolder);
            panelArea.setFitToWidth(true);
            panelArea.setHbarPolicy(ScrollPane.ScrollBarPolicy.NEVER);
            panelHolder.getStyleClass().add("settings-panel-holder");
            panelHolder.getChildren().add(new Label("empty"));
            setCenter(panelArea);

            treeSettingsPanels.setShowRoot(true);
            treeSettingsPanels.setCellFactory(this::createCell);
            buildTree(providers);

            HBox searchRow = new HBox(6, new Label("Search: "), txtSearch);
            searchRow.getStyleClass().add("settings-search-row");
            VBox westPanel = new VBox(6, searchRow, treeSettingsPanels);
            westPanel.getStyleClass().add("settings-tree-panel");
            VBox.setVgrow(treeSettingsPanels, javafx.scene.layout.Priority.ALWAYS);
            setLeft(westPanel);

            treeSettingsPanels.getSelectionModel().selectedItemProperty()
                    .addListener((obs, old, item) -> {
                        if (item == null) {
                            return;
                        }
                        SettingsProviderF provider = item.getValue();
                        if (provider != null) {
                            setSettingsPanel(provider.getPanel(mainWindow));
                        }
                    });
        }

        private TreeCell<SettingsProviderF> createCell(
                javafx.scene.control.TreeView<SettingsProviderF> view) {
            return new TreeCell<>() {
                @Override
                protected void updateItem(SettingsProviderF item, boolean empty) {
                    super.updateItem(item, empty);
                    getStyleClass().remove("settings-tree-match");
                    if (empty) {
                        setText(null);
                        return;
                    }
                    if (item == null) {
                        // the invisible root carries no provider; Swing labels it "KeY Settings"
                        setText("KeY Settings");
                        return;
                    }
                    setText(item.getDescription());
                    String search = txtSearch.getText();
                    if (!search.isEmpty() && item.contains(search)) {
                        getStyleClass().add("settings-tree-match");
                    }
                }
            };
        }

        private void buildTree(List<SettingsProviderF> providers) {
            TreeItem<SettingsProviderF> root = new TreeItem<>(null);
            root.setExpanded(true);
            for (SettingsProviderF provider : providers) {
                root.getChildren().add(createItem(provider));
            }
            treeSettingsPanels.setRoot(root);
            if (!providers.isEmpty()) {
                // Swing shows the first provider's panel initially
                setSettingsPanel(providers.get(0).getPanel(mainWindow));
                treeSettingsPanels.getSelectionModel().select(1);
            }
        }

        private TreeItem<SettingsProviderF> createItem(SettingsProviderF provider) {
            TreeItem<SettingsProviderF> item = new TreeItem<>(provider);
            item.setExpanded(true);
            providerByItem.put(item, provider);
            provider.getChildProviders().forEach(child -> item.getChildren()
                    .add(createItem(child)));
            return item;
        }

        private void setSettingsPanel(javafx.scene.Node comp) {
            panelHolder.getChildren().setAll(comp);
            panelArea.setVvalue(0);
        }

        /**
         * Selects the given provider in the tree (Swing {@code SettingsUi.selectPanel}).
         *
         * @param provider the provider to select
         */
        void selectPanel(SettingsProviderF provider) {
            findItem(treeSettingsPanels.getRoot(), provider)
                    .ifPresent(item -> treeSettingsPanels.getSelectionModel().select(item));
        }

        private java.util.Optional<TreeItem<SettingsProviderF>> findItem(
                TreeItem<SettingsProviderF> node, SettingsProviderF provider) {
            if (node.getValue() == provider) {
                return java.util.Optional.of(node);
            }
            for (TreeItem<SettingsProviderF> child : node.getChildren()) {
                var found = findItem(child, provider);
                if (found.isPresent()) {
                    return found;
                }
            }
            return java.util.Optional.empty();
        }
    }
}
