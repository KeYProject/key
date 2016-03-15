package de.uka.ilkd.key.nui.controller;

import java.util.Observable;
import java.util.Observer;

import javafx.collections.ObservableList;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.fxml.FXML;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.ListView;
import javafx.scene.control.MenuItem;
import javafx.scene.control.TextArea;
import javafx.scene.input.MouseEvent;

/**
 * 
 * @author Florian Breitfelder
 *
 */
@ControllerAnnotation(createMenu = true)
public class OpenProofsViewController extends NUIController
        implements Observer {

    @FXML
    TextArea textAreaOpenProofs;

    @FXML
    ListView<String> listView;

    private ContextMenu contextMenu;

    @Override
    protected void init() {
        dataModel.addObserver(this);
        listView.setOnMouseClicked(new EventHandler<MouseEvent>() {
            @Override
            public void handle(MouseEvent event) {
                String selectedItem = listView.getSelectionModel()
                        .getSelectedItem();
                if (selectedItem != null) {
                    dataModel.loadProofFormMemory(selectedItem);
                }
            }
        });
        MenuItem deleteProof = new MenuItem(bundle.getString("closeProof"));
        contextMenu = new ContextMenu(deleteProof);
        deleteProof.setOnAction(new EventHandler<ActionEvent>() {
            @Override
            public void handle(ActionEvent event) {
                dataModel.deleteProof(listView.getSelectionModel()
                        .getSelectedItem().toString());
            }
        });
    }

    @Override
    public void update(Observable o, Object arg) {
        ObservableList<String> loadedProofs = dataModel.getListOfProofs();
        if (loadedProofs.size() >= 1) {
            listView.setContextMenu(contextMenu);
        }
        else {
            listView.setContextMenu(null);
        }
        listView.setItems(loadedProofs);
        listView.getSelectionModel().select(arg.toString());
    }

}
