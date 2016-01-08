package de.uka.ilkd.key.nui.controller;

import java.net.URL;
import java.util.ResourceBundle;

import javafx.application.Platform;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.Initializable;
import javafx.scene.control.Button;
import javafx.scene.control.TextField;

public class SearchViewController implements Initializable {

    @FXML
    TextField SearchTextField;
    @FXML
    Button PreviousButton;
    @FXML
    Button NextButton;
    @FXML
    Button SearchButton;

    TreeViewController treeViewController = TreeViewController.getInstance();

    private static SearchViewController instance;

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        Platform.runLater(new Runnable() {
            @Override
            public void run() {
                SearchTextField.requestFocus();
            }
        });
        SearchTextField.textProperty()
                .addListener(new ChangeListener<String>() {
                    @Override
                    public void changed(
                            ObservableValue<? extends String> observable,
                            String oldValue, String newValue) {
                        SearchButton.setDisable(newValue.isEmpty());
                        if(newValue.isEmpty()){
                            NextButton.setDisable(true);
                            PreviousButton.setDisable(true);
                        }
                    }
                });
        SearchButton.setDisable(true);

        instance = this;
    }

    public void handleSearchButton(ActionEvent e) {
        if (!SearchButton.isDisable())
            treeViewController.search(SearchTextField.getText());
    }

    public void handleNextButton(ActionEvent e) {
        treeViewController.gotoNextSearchResult();
    }

    public void handlePreviousButton(ActionEvent e) {
        treeViewController.gotoPreviousSearchResult();
    }

    /**
     * TODO remove this bad practice singleton
     */
    static SearchViewController getInstance() {
        return instance;
    }
}
