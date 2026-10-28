/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.dialogs;

import java.util.List;
import java.util.concurrent.CountDownLatch;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.CheckBox;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.stage.Modality;
import javafx.stage.Stage;

import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.lemma.TacletSoundnessPOLoader.TacletFilter;
import de.uka.ilkd.key.taclettranslation.lemma.TacletSoundnessPOLoader.TacletInfo;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.javafx.FxUtil;

/**
 * lemma (P2b, A2): JavaFX port of the Swing {@code LemmaSelectionDialog}
 * (key.ui lemmatagenerator/LemmaSelectionDialog.java, 161 lines) — the modal "Taclet Selection"
 * dialog of the lemma-generation workflow, implementing {@link TacletFilter}: the user picks the
 * taclets the soundness proof obligations are created for, via an {@link ItemChooserF} with the
 * "Show only supported taclets." filter checkbox (the default filter of the Swing dialog) and
 * the "already in use"/"not supported" moving restriction.
 * <p>
 * Swing runs the modal dialog from the loader thread (the {@code TacletSoundnessPOLoader} calls
 * {@link #filter} on its own thread); the FX port marshals the dialog to the FX thread and
 * blocks the caller with a latch.
 */
public class LemmaSelectionDialogF implements TacletFilter {

    private final ItemChooserF<TacletInfo> tacletChooser =
        new ItemChooserF<>("Search for taclets with names containing");

    private final ItemChooserF.ItemFilter<TacletInfo> showOnlySupportedTaclets =
        itemData -> !itemData.isNotSupported();

    private final ItemChooserF.ItemFilter<TacletInfo> filterForMovingTaclets =
        itemData -> !itemData.isNotSupported() && !itemData.isAlreadyInUse();

    private final Stage stage = new Stage();
    private boolean cancelled = false;
    private ImmutableSet<Taclet> lastFilterResult = null;

    public LemmaSelectionDialogF() {
        stage.setTitle("Taclet Selection");
        tacletChooser.addFilterForMovingItems(filterForMovingTaclets);
        tacletChooser.addFilter(showOnlySupportedTaclets);

        CheckBox showSupported = new CheckBox("Show only supported taclets.");
        showSupported.setSelected(true);
        showSupported.setOnAction(e -> {
            if (showSupported.isSelected()) {
                tacletChooser.addFilter(showOnlySupportedTaclets);
            } else {
                tacletChooser.removeFilter(showOnlySupportedTaclets);
            }
        });

        Button okButton = new Button("OK");
        okButton.setOnAction(e -> stage.close());
        Button cancelButton = new Button("Cancel");
        cancelButton.setOnAction(e -> {
            // Swing cancel(): remove the selection and move everything back to the left
            tacletChooser.removeSelection();
            tacletChooser.moveAllToLeft();
            cancelled = true;
            stage.close();
        });
        HBox buttonPanel = new HBox(8, showSupported, okButton, cancelButton);
        buttonPanel.setAlignment(Pos.CENTER_RIGHT);
        buttonPanel.setPadding(new Insets(6));

        BorderPane root = new BorderPane();
        root.setCenter(tacletChooser);
        root.setBottom(buttonPanel);
        Scene scene = new Scene(root, 700, 500);
        ThemeManager.getInstance().style(scene);
        stage.setScene(scene);
        stage.setMinWidth(300);
        stage.setMinHeight(300);
    }

    /**
     * Swing {@code showModal} (LemmaSelectionDialog.java:59-68): fills the chooser, shows the
     * modal dialog and returns the taclets of the selected (right-side) items.
     *
     * @param taclets the candidate taclet infos
     * @return the selected taclets
     */
    public ImmutableSet<Taclet> showModal(List<TacletInfo> taclets) {
        cancelled = false;
        tacletChooser.setItems(taclets, "Taclets");
        stage.initModality(Modality.APPLICATION_MODAL);
        stage.showAndWait();
        ImmutableSet<Taclet> set = DefaultImmutableSet.nil();
        for (TacletInfo info : tacletChooser.getDataOfSelectedItems()) {
            set = set.add(info.getTaclet());
        }
        lastFilterResult = set;
        return set;
    }

    /** @return the result of the last {@link #filter} call (verification harness). */
    public ImmutableSet<Taclet> lastFilterResult() {
        return lastFilterResult;
    }

    /** @return the internal chooser (verification harness). */
    public ItemChooserF<TacletInfo> getTacletChooser() {
        return tacletChooser;
    }

    /** @return whether the modal stage is currently showing (verification harness). */
    public boolean isShowing() {
        return stage.isShowing();
    }

    /** Swing {@code cancel()} state (for the verification harness). */
    public boolean isCancelled() {
        return cancelled;
    }

    /** Closes the dialog as if OK had been pressed (verification harness). */
    public void requestOk() {
        stage.close();
    }

    /** Closes the dialog as if Cancel had been pressed (verification harness). */
    public void requestCancel() {
        // Swing cancel(): remove the selection and move everything back to the left
        tacletChooser.removeSelection();
        tacletChooser.moveAllToLeft();
        cancelled = true;
        stage.close();
    }

    /** @return the stage (verification harness) */
    public Stage getStage() {
        return stage;
    }

    @Override
    public ImmutableSet<Taclet> filter(List<TacletInfo> taclets) {
        // the TacletSoundnessPOLoader calls filter on its own thread — marshal the modal
        // dialog to the FX thread and block until it is closed
        if (FxUtil.isFxThread()) {
            return showModal(taclets);
        }
        ImmutableSet<Taclet>[] result = new ImmutableSet[1];
        CountDownLatch latch = new CountDownLatch(1);
        FxUtil.runLater(() -> {
            try {
                result[0] = showModal(taclets);
            } finally {
                latch.countDown();
            }
        });
        try {
            latch.await();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return DefaultImmutableSet.nil();
        }
        return result[0];
    }
}
