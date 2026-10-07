/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.settings;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonBar;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.StackPane;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.Window;

/**
 * Aggregates the registered {@link SettingsProviderF}s and opens the settings dialog, counter-part
 * of {@code SettingsManager}/{@code SettingsDialog} of the Swing module {@code key.ui}.
 * <p>
 * The dialog is built in code (no FXML): a tree of categories on the left (implemented via
 * {@link TreeView}), the selected provider's panel on the right, and OK / Apply / Cancel controls.
 */
public final class SettingsManagerF {

    private static final SettingsManagerF INSTANCE = new SettingsManagerF();

    private final List<SettingsProviderF> providers = new ArrayList<>();
    private final TreeMap<String, List<SettingsProviderF>> providersByCategory = new TreeMap<>();

    private SettingsManagerF() {
    }

    /**
     * @return the global settings manager instance
     */
    public static SettingsManagerF getInstance() {
        return INSTANCE;
    }

    /**
     * Registers a settings provider.
     *
     * @param provider the provider to register
     */
    public void addProvider(SettingsProviderF provider) {
        providers.add(provider);
        providersByCategory
                .computeIfAbsent(provider.getCategory() == null ? "" : provider.getCategory(),
                    key -> new ArrayList<>())
                .add(provider);
    }

    /**
     * Registers multiple settings providers.
     *
     * @param providers the providers to register
     */
    public void addProviders(List<SettingsProviderF> providers) {
        providers.forEach(this::addProvider);
    }

    /**
     * @return the currently registered providers, in registration order
     */
    public List<SettingsProviderF> getProviders() {
        return List.copyOf(providers);
    }

    /**
     * Applies all registered providers; used by auto mode and profile loading.
     */
    public void applyAll() {
        providers.forEach(SettingsProviderF::apply);
    }

    /**
     * Opens the settings dialog, modal to the given owner window.
     *
     * @param owner the owner window, or {@code null} for a standalone dialog
     */
    public void openSettings(Window owner) {
        Stage stage = new Stage();
        stage.initOwner(owner);
        stage.initModality(Modality.WINDOW_MODAL);
        stage.setTitle("KeY - Settings");

        BorderPane content = new BorderPane();
        content.setPadding(new Insets(10));

        Map<TreeItem<String>, SettingsProviderF> providerByItem = new IdentityHashMap<>();
        TreeView<String> tree = buildTree(providerByItem);
        content.setLeft(tree);
        BorderPane.setMargin(tree, new Insets(0, 10, 0, 0));

        ScrollPane scrollPane = new ScrollPane();
        scrollPane.setFitToWidth(true);
        StackPane panelArea = new StackPane();
        scrollPane.setContent(panelArea);
        content.setCenter(scrollPane);
        BorderPane.setAlignment(scrollPane, Pos.CENTER);

        tree.getSelectionModel().selectedItemProperty().addListener((obs, old, selected) -> {
            SettingsProviderF provider = selected == null ? null : providerByItem.get(selected);
            if (provider != null) {
                panelArea.getChildren().setAll(provider.getPanel());
            }
        });

        ButtonBar buttons = new ButtonBar();
        Button okButton = new Button("OK");
        Button applyButton = new Button("Apply");
        Button cancelButton = new Button("Cancel");
        ButtonBar.setButtonData(okButton, ButtonBar.ButtonData.OK_DONE);
        ButtonBar.setButtonData(applyButton, ButtonBar.ButtonData.APPLY);
        ButtonBar.setButtonData(cancelButton, ButtonBar.ButtonData.CANCEL_CLOSE);
        buttons.getButtons().addAll(okButton, applyButton, cancelButton);

        applyButton.setOnAction(ignored -> providers.forEach(SettingsProviderF::apply));
        okButton.setOnAction(ignored -> {
            providers.forEach(SettingsProviderF::apply);
            stage.close();
        });
        cancelButton.setOnAction(ignored -> stage.close());

        content.setBottom(buttons);

        stage.setScene(new javafx.scene.Scene(content, 900, 600));
        selectFirstNonEmpty(tree);
        stage.show();
    }

    private TreeView<String> buildTree(Map<TreeItem<String>, SettingsProviderF> providerByItem) {
        TreeItem<String> root = new TreeItem<>("Settings");
        root.setExpanded(true);

        for (var entry : providersByCategory.entrySet()) {
            TreeItem<String> categoryItem = new TreeItem<>(entry.getKey());
            categoryItem.setExpanded(true);
            entry.getValue().stream()
                    .sorted(Comparator.comparing(SettingsProviderF::getDescription))
                    .forEach(provider -> {
                        TreeItem<String> item = new TreeItem<>(provider.getDescription());
                        providerByItem.put(item, provider);
                        categoryItem.getChildren().add(item);
                    });
            root.getChildren().add(categoryItem);
        }

        TreeView<String> tree = new TreeView<>(root);
        tree.setShowRoot(false);
        tree.setPrefWidth(260);
        return tree;
    }

    private void selectFirstNonEmpty(TreeView<String> tree) {
        TreeItem<String> root = tree.getRoot();
        if (root != null && !root.getChildren().isEmpty()) {
            TreeItem<String> firstCategory = root.getChildren().get(0);
            if (!firstCategory.getChildren().isEmpty()) {
                tree.getSelectionModel().select(firstCategory.getChildren().get(0));
            }
        }
    }
}
