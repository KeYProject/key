package de.uka.ilkd.key.nui.exceptions;

import javafx.scene.control.Alert;
import javafx.scene.control.Alert.AlertType;

public class NUIException extends Exception {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    public void showMessage() {
        Alert alert = new Alert(AlertType.ERROR);
        alert.setTitle("KeY exception");
        alert.setHeaderText("");
        alert.setContentText(getMessage());
        alert.showAndWait();
    }
}
