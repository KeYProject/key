package de.uka.ilkd.key.nui.controller;

import java.net.URL;
import java.util.ResourceBundle;

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
    
    @Override
    public void initialize(URL location, ResourceBundle resources) {
       SearchTextField.requestFocus();
       SearchButton.setDisable(false);
    }
    
    public void handleSearchButton(ActionEvent e){
        TreeViewController.getInstance().search(SearchTextField.getText());
    }
    
    public void handleNextButton(ActionEvent e){
        System.out.println("'>' Button was pressed");
    }
    
    public void handlePreviousButton(ActionEvent e){
        System.out.println("'<' Button was pressed");
    }
}
