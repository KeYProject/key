/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.utilities;

import java.awt.*;
import java.util.LinkedList;
import java.util.List;
import javax.swing.*;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;


/**
 * This class offers a simple solution for receiving checked user input. It describes a panel
 * consisting of a text field for user input and a traffic light. By means of the interface
 * <code>CheckedUserInputInspector</code> one can check the input the user makes instantaneously.
 *
 * If you want to see how the component looks like, execute the method <code>main</code> at the
 * bottom of this file.
 */
public class CheckedUserInput extends JPanel {
    private static final long serialVersionUID = 1L;



    public interface CheckedUserInputInspector {

        String NO_USER_INPUT = " ";

        /**
         * @param toBeChecked the user input to be checked.
         * @return <code>null</code> if the user input is valid, otherwise a string describing the
         *         error.
         */
        String check(String toBeChecked);


    }

    /**
     * Used for observing the checked user input.
     */
    public interface CheckedUserInputListener {
        void userInputChanged(String input, boolean valid, String reason);


    }


    private TrafficLight trafficLight;
    private JTextPane inputFieldForFormula;
    private ClickableMessageBox infoBox;

    private JScrollPane detailScrollPane;


    private CheckedUserInputInspector inspector;
    private final List<CheckedUserInputListener> listeners =
        new LinkedList<>();

    public CheckedUserInput(boolean showInformation) {
        this(toBeChecked -> null, showInformation);

    }

    public CheckedUserInput(CheckedUserInputInspector inspector, boolean showInformation) {
        this.inspector = inspector;
        this.setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));
        Box horzBox = Box.createHorizontalBox();
        JScrollPane pane = new JScrollPane(getInputFieldForFormula());
        horzBox.add(pane);
        horzBox.add(Box.createHorizontalStrut(5));
        horzBox.add(getTrafficLight());
        Dimension dim = pane.getPreferredSize();
        dim.height = getTrafficLight().getPreferredSize().height;
        pane.setPreferredSize(dim);
        pane.setMinimumSize(dim);
        this.add(horzBox);
        this.add(Box.createVerticalStrut(2));


        if (showInformation) {
            horzBox = Box.createHorizontalBox();
            horzBox.add(Box.createHorizontalStrut(5));
            horzBox.add(Box.createHorizontalGlue());
            this.add(horzBox);
            horzBox = Box.createHorizontalBox();
            horzBox.add(getDetailScrollPane());
            horzBox.add(Box.createHorizontalGlue());
            this.add(horzBox);
            this.add(Box.createVerticalGlue());
        }

        setInput("");
    }

    public void setInspector(CheckedUserInputInspector inspector) {
        this.inspector = inspector;
        checkInput();
    }

    public JScrollPane getDetailScrollPane() {
        if (detailScrollPane == null) {
            detailScrollPane = new JScrollPane(getInfoBox());
            detailScrollPane.setMaximumSize(new Dimension(Integer.MAX_VALUE, Integer.MAX_VALUE));
            detailScrollPane
                    .setPreferredSize(new Dimension(detailScrollPane.getPreferredSize().width, 80));
            detailScrollPane
                    .setMinimumSize(new Dimension(detailScrollPane.getPreferredSize().width, 80));
            detailScrollPane.setBorder(BorderFactory.createTitledBorder("Details"));
        }
        return detailScrollPane;
    }


    private TrafficLight getTrafficLight() {
        if (trafficLight == null) {
            trafficLight = new TrafficLight(10);
        }
        return trafficLight;
    }

    private ClickableMessageBox getInfoBox() {
        if (infoBox == null) {
            infoBox = new ClickableMessageBox();
            infoBox.setBackground(this.getBackground());
            infoBox.setFont(this.getFont());
            infoBox.add(object -> {
                if (object != null) {
                    JOptionPane.showMessageDialog(detailScrollPane, object,
                        "Problem Description", JOptionPane.INFORMATION_MESSAGE);
                }
            });

        }
        return infoBox;
    }



    private JTextPane getInputFieldForFormula() {
        if (inputFieldForFormula == null) {
            inputFieldForFormula = new JTextPane();
            inputFieldForFormula.getDocument().addDocumentListener(new DocumentListener() {

                @Override
                public void removeUpdate(DocumentEvent e) {
                    checkInput();

                }

                @Override
                public void insertUpdate(DocumentEvent e) {
                    checkInput();

                }

                @Override
                public void changedUpdate(DocumentEvent e) {

                }
            });

        }
        return inputFieldForFormula;
    }

    private void checkInput() {
        String text = inputFieldForFormula.getText();
        String result = inspector.check(text);
        setValid(result);
        for (CheckedUserInputListener listener : listeners) {
            listener.userInputChanged(text, result == null, result);
        }
    }

    public void addListener(CheckedUserInputListener listener) {
        listeners.add(listener);
    }


    public void removeListener(CheckedUserInputListener listener) {
        listeners.remove(listener);
    }

    public String getInput() {
        return getInputFieldForFormula().getText();
    }

    public void setInput(String input) {
        getInputFieldForFormula().setText((input == null) ? "" : input);
        checkInput();
    }

    private void setValid(String result) {
        getInfoBox().clear();
        if (result != null) {
            String[] segments = result.split("#");
            getInfoBox().add(segments.length >= 2 ? segments[1] : null, segments[0], Color.RED);

        }
        getTrafficLight().setGreen(result == null);

    }

    public static String showAsDialog(String title, String description, final String helpText,
            String defaultInput, CheckedUserInputInspector inspector, boolean showInformation

    ) {
        CheckedUserInput userInput = new CheckedUserInput(inspector, showInformation);

        Box vertBox = Box.createVerticalBox();
        if (description != null) {
            Box horzBox = Box.createHorizontalBox();
            horzBox.add(new JLabel(description));
            horzBox.add(Box.createHorizontalGlue());
            vertBox.add(horzBox);
            vertBox.add(Box.createVerticalStrut(5));
        }
        vertBox.add(userInput);
        final StdDialog dialog = new StdDialog(title, vertBox, 5, helpText != null);
        userInput.addListener((input, valid, reason) -> dialog.getOkButton().setEnabled(valid));

        dialog.getHelpButton()
                .addActionListener(e -> JOptionPane.showMessageDialog(dialog, helpText, "Help",
                    JOptionPane.INFORMATION_MESSAGE));

        userInput.setInput(defaultInput);
        Dimension dim = dialog.getPreferredSize();
        dialog.setSize(Math.max(dim.width, dialog.getOkButton().getWidth() * 4), dim.height);
        dialog.setVisible(true);

        if (dialog.okButtonHasBeenPressed()) {
            return userInput.getInput();
        }
        return null;
    }



    public static void main(String[] args) {
        showAsDialog("Checked user input embedded in a dialog.", "type 'test'",
            "that is only a test", "default",
            toBeChecked -> toBeChecked.equals("test") ? null : "Syntax Error#test", true);
    }
}
