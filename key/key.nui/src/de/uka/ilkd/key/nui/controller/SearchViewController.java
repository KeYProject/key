package de.uka.ilkd.key.nui.controller;

import java.net.URL;

import java.util.ResourceBundle;
import de.uka.ilkd.key.nui.ComponentFactory;
import javafx.application.Platform;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.Initializable;
import javafx.scene.control.Button;
import javafx.scene.control.TextField;
import javafx.scene.input.KeyCode;

public class SearchViewController implements Initializable {

    public static final String NAME = ".searchView";

    public static final String RESOURCE = ".searchView.fxml";

    @FXML
    TextField SearchTextField;
    @FXML
    Button PreviousButton;
    @FXML
    Button NextButton;

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        NUIController.getInstance().registerKeyListener(KeyCode.ENTER,
                new KeyCode[] {}, (event) -> {
                    if(event.isShiftDown()){
                        PreviousButton.fire();    
                    } else {
                        NextButton.fire();
                    }
                });

        Platform.runLater(() -> {
            SearchTextField.requestFocus();
        });

        SearchTextField.textProperty().addListener((obs, oldText, newText) -> {
            NextButton.setDisable(newText.isEmpty());
            PreviousButton.setDisable(newText.isEmpty());
            TreeViewController tVC = ComponentFactory.getInstance()
                    .getController(TreeViewController.NAME);
            tVC.search(newText);
        });
    }

    /**
     * To be called if the NextButton is clicked.
     * 
     * @param e
     *            the <tt>ActionEvent</tt> being fired by clicking that button.
     */
    public void handleNextButton(ActionEvent e) {
        TreeViewController t = ComponentFactory.getInstance()
                .getController(TreeViewController.NAME);
        t.selectAndIfNeededScrollToNextSearchResult();
    }

    /**
     * To be called if the PreviousButton is clicked.
     * 
     * TODO currently does not work
     * 
     * @param e
     *            the <tt>ActionEvent</tt> being fired by clicking that button.
     */
    public void handlePreviousButton(ActionEvent e) {
        TreeViewController t = ComponentFactory.getInstance()
                .getController(TreeViewController.NAME);
        t.selectAndIfNeededScrollToPreviousSearchResult();
    }

    /**
     * request the focus for the TextField controlled by <tt>this</tt>
     */
    public void performFocusRequest() {
        SearchTextField.requestFocus();
    }
}
