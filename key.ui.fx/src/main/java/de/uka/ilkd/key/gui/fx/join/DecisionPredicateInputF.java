/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.join;

import java.util.LinkedList;
import java.util.List;

import javafx.geometry.Insets;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.TextField;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;

/**
 * A text field for user input with instantaneous validity feedback (a "traffic light"). The
 * check function is supplied by an {@link InspectorF}; every change of the input re-runs the
 * check and notifies the registered {@link ListenerF}s.
 * <p>
 * Counter-part of {@code de.uka.ilkd.key.gui.utilities.CheckedUserInput} in the Swing module
 * {@code key.ui} (CheckedUserInput.java:23-248). Deviations:
 * <ul>
 * <li>the input field is a single-line {@link TextField} instead of a {@code JTextPane} (the
 * join dialog only enters single decision formulae);</li>
 * <li>the Swing traffic light ({@code TrafficLight}) becomes a colored dot label styled by CSS
 * ({@code .traffic-light-ok} / {@code .traffic-light-error});</li>
 * <li>the optional "Details" area ({@code showInformation} flag of the Swing constructor,
 * CheckedUserInput.java:63-97) is not ported — the join dialog always constructs the input with
 * {@code showInformation = false} (JoinDialog.java:314) and shows the messages in its own info
 * box instead.</li>
 * </ul>
 * The listener contract ({@code userInputChanged(input, valid, reason)} with {@code reason ==
 * null} iff valid) and the red "reason#detail" message convention (CheckedUserInput.java:197-206)
 * are ported unchanged.
 */
public final class DecisionPredicateInputF extends VBox {

    /** Inspects user input; returns {@code null} iff the input is valid. */
    public interface InspectorF {

        /** Returned instead of an error if nothing has been entered yet. */
        String NO_USER_INPUT = " ";

        /**
         * @param toBeChecked the user input to be checked
         * @return {@code null} if the user input is valid, otherwise a string describing the
         *         error
         */
        String check(String toBeChecked);
    }

    /** Observes the checked user input (Swing CheckedUserInput.CheckedUserInputListener). */
    public interface ListenerF {
        void userInputChanged(String input, boolean valid, String reason);
    }

    private final TextField inputField = new TextField();
    private final Label trafficLight = new Label();

    private InspectorF inspector = toBeChecked -> null;
    private final List<ListenerF> listeners = new LinkedList<>();

    public DecisionPredicateInputF() {
        HBox inputRow = new HBox(5);
        inputRow.getChildren().addAll(inputField, trafficLight);
        HBox.setHgrow(inputField, Priority.ALWAYS);
        trafficLight.getStyleClass().add("traffic-light");
        trafficLight.setMinSize(10, 10);
        getChildren().add(inputRow);
        setPadding(new Insets(0, 0, 2, 0));

        // Swing installs a DocumentListener on the text component that runs checkInput on every
        // change (CheckedUserInput.java:146-168); the FX equivalent listens on the text property.
        inputField.textProperty().addListener((obs, oldV, newV) -> checkInput());
        setInput("");
    }

    /** Swing CheckedUserInput.setInspector (CheckedUserInput.java:99-102). */
    public void setInspector(InspectorF inspector) {
        this.inspector = inspector;
        checkInput();
    }

    public void addListener(ListenerF listener) {
        listeners.add(listener);
    }

    public void removeListener(ListenerF listener) {
        listeners.remove(listener);
    }

    /** Swing CheckedUserInput.getInput (CheckedUserInput.java:188-190). */
    public String getInput() {
        return inputField.getText();
    }

    /** Swing CheckedUserInput.setInput (CheckedUserInput.java:192-195). */
    public void setInput(String input) {
        inputField.setText(input == null ? "" : input);
        checkInput();
    }

    /**
     * Swing CheckedUserInput.checkInput (CheckedUserInput.java:170-177): re-run the inspector
     * and notify the listeners.
     */
    private void checkInput() {
        String text = inputField.getText();
        String result = inspector.check(text);
        setValid(result);
        for (ListenerF listener : listeners) {
            listener.userInputChanged(text, result == null, result);
        }
    }

    /**
     * Swing CheckedUserInput.setValid (CheckedUserInput.java:197-206): red message on error
     * (the "reason#detail" convention), green traffic light on success.
     */
    private void setValid(String result) {
        boolean valid = result == null;
        trafficLight.getStyleClass().removeAll(List.of("traffic-light-ok", "traffic-light-error"));
        trafficLight.getStyleClass().add(valid ? "traffic-light-ok" : "traffic-light-error");
    }

    /** Exposes the input field for tests (the traffic light dot is {@link #getTrafficLight()}). */
    public TextField getInputField() {
        return inputField;
    }

    /** Exposes the traffic light for tests. */
    public Node getTrafficLight() {
        return trafficLight;
    }
}
