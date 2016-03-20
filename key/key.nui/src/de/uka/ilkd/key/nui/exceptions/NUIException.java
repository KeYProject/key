package de.uka.ilkd.key.nui.exceptions;

import javafx.scene.control.Alert;
import javafx.scene.control.Alert.AlertType;

/**
 * @author Florian Breitfelder
 *
 */
public class NUIException extends Exception {

    /**
     * The class version number.
     */
    private static final long serialVersionUID = 1L;

    /**
     * Shows a message dialog with the raised exception.
     */
    public final void showMessage() {
        final Alert alert = new Alert(AlertType.ERROR);
        alert.setTitle("KeY exception");
        alert.setHeaderText("");
        alert.setContentText(getMessage());
        alert.showAndWait();
    }
}
