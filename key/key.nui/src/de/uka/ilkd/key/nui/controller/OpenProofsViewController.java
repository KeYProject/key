package de.uka.ilkd.key.nui.controller;

import java.text.MessageFormat;
import java.util.Observable;
import java.util.Observer;
import java.util.Optional;

import de.uka.ilkd.key.nui.exceptions.ControllerNotFoundException;
import javafx.collections.ObservableList;
import javafx.fxml.FXML;
import javafx.scene.control.Alert;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.control.ButtonType;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.ListView;
import javafx.scene.control.MenuItem;
import javafx.scene.layout.Pane;

/**
 * Controller for the view showing an overview of all loaded proofs.
 * 
 * @author Florian Breitfelder
 */
@ControllerAnnotation(createMenu = true)
public class OpenProofsViewController extends NUIController
        implements Observer {

    /**
     * The context menu shown when the user right-clicks on an loaded proof.
     */
    private ContextMenu contextMenu;
    @FXML
    private transient ListView<String> listView;

    @FXML
    private Pane openProofsViewPane;

    /**
     * Getter.
     * 
     * @return the {@link ContextMenu}.
     */
    public ContextMenu getContextMenu() {
        return contextMenu;
    }

    /**
     * Getter.
     * 
     * @param contextMenu
     *            the {@link ContextMenu} you want to set.
     */
    public void setContextMenu(final ContextMenu contextMenu) {
        this.contextMenu = contextMenu;
    }

    @Override
    public void update(final Observable observable, final Object arg) {
        final ObservableList<String> loadedProofs = getDataModel()
                .getListOfProofs();
        if (loadedProofs.size() >= 1) {
            listView.setContextMenu(contextMenu);
        }
        else {
            listView.setContextMenu(null);
        }
        listView.setItems(loadedProofs);
        listView.getSelectionModel().select(arg.toString());
    }

    /**
     * Shows the save dialog after the user closed a proof via the
     * {@link #contextMenu}. The caller must check if the file was modified at
     * all, e.g. {@code getDataModel().getLoadedTreeViewState().isModified()}.
     * 
     * @param returns
     *            true iff the open proof was saved successful or the user
     *            aborted ("cancel") the "save as" file chooser window
     */
    private boolean showSaveDialog() {
        // File was changed: ask user if he wants to save changes
        // create alert window
        final Alert alert = new Alert(AlertType.CONFIRMATION);
        alert.setTitle(getBundle().getString("dialogTitle"));

        // define text for header and content area
        final String filename = getDataModel().getLoadedTreeViewState()
                .getProof().getProofFile().getName();
        alert.setHeaderText(MessageFormat.format(
                getBundle().getString("dialogHeader"), "'" + filename + "'"));
        alert.setContentText(getBundle().getString("dialogQuestion"));

        // define button types
        final ButtonType buttonSaveAs = new ButtonType(
                getBundle().getString("dialogSaveAs"));
        final ButtonType buttonClose = new ButtonType(
                getBundle().getString("dialogExit"));
        final ButtonType buttonAbort = new ButtonType(
                getBundle().getString("dialogAbort"));
        alert.getButtonTypes().setAll(buttonSaveAs, buttonClose, buttonAbort);

        // evaluate button user clicked
        final Optional<ButtonType> result = alert.showAndWait();
        boolean returnValue = false;
        if (result.get() == buttonSaveAs) {
            try {
                returnValue = ((MainViewController) getNui()
                        .getController("MainView")).saveProofAsDialog();
            }
            catch (ControllerNotFoundException e) {
                e.showMessage();
            }
        }
        else if (result.get() == buttonClose) {
            returnValue = true;
        }

        // If NO/CANCEL was selected (or in any other case): just close the
        // loaded proof
        alert.close();

        return returnValue;
    }

    @Override
    protected void init() {
        getDataModel().addObserver(this);
        // Action to be performed if user clicks (left) on a proof entry
        listView.setOnMouseClicked((event) -> {
            final String selectedItem = listView.getSelectionModel()
                    .getSelectedItem();
            if (selectedItem != null) {
                getDataModel().loadProofFormMemory(selectedItem);
            }
        });

        final MenuItem deleteProof = new MenuItem(
                getBundle().getString("closeProof"));
        contextMenu = new ContextMenu(deleteProof);

        // Action to be performed if user clicks on 'Close Proof' (contextMenu)
        deleteProof.setOnAction((event) -> {
            boolean canBeClosed = false;
            // only show save dialog if proof was modified
            if (getDataModel().getLoadedTreeViewState().isModified()) {
                canBeClosed = showSaveDialog();
            }
            // if proof was modified and saved OR if proof was not modified at
            // all, then remove proof from openProofsView
            if (canBeClosed
                    || !getDataModel().getLoadedTreeViewState().isModified()) {
                getDataModel().removeProof(
                        listView.getSelectionModel().getSelectedItem());
            }
        });
    }

}
