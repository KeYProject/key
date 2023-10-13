/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.settings;


import java.awt.*;
import java.io.File;
import java.util.Arrays;
import java.util.List;
import javax.annotation.Nullable;
import javax.swing.*;

import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;

import net.miginfocom.layout.AC;
import net.miginfocom.layout.CC;
import net.miginfocom.layout.LC;
import net.miginfocom.swing.MigLayout;

/**
 * Extension of {@link SimpleSettingsPanel} which uses {@link MigLayout} to create a nice
 * three-column view.
 * <p>
 * Allows a simple building of the UI by defining several factory methods, e.g.
 * {@link #addTextField(String, String, String, Validator)}
 * <p>
 * 2019-04-08, weigl: rewrite to mig layout
 *
 * @author weigl
 */
public abstract class SettingsPanel extends SimpleSettingsPanel {
    private static final long serialVersionUID = 3465371513326517504L;

    protected SettingsPanel() {
        pCenter.setLayout(new MigLayout(
            // set up rows:
            new LC().fillX()
                    // remove the padding after the help icon
                    .insets(null, null, null, "0").wrapAfter(3),
            // set up columns:
            new AC().count(3).fill(1)
                    // label column does not grow
                    .grow(0f, 0)
                    // input area does grow
                    .grow(1000f, 1)
                    // help icon always has the same size
                    .size("16px", 2)
                    .align("right", 0)));
    }

    /**
     * @param info
     * @return
     */
    protected static JTextArea createInfoArea(String info) {
        JTextArea textArea = new JTextArea(info);
        // textArea.setBackground(this.getBackground());
        textArea.setEditable(false);
        textArea.setLineWrap(true);
        textArea.setWrapStyleWord(true);
        return textArea;
    }

    /**
     * @param info
     * @param components
     */
    protected void addRowWithHelp(String info, JComponent... components) {
        boolean hasInfo = info != null && !info.isEmpty();
        for (JComponent component : components) {
            component.setAlignmentX(LEFT_ALIGNMENT);
            // last component, either line break or info
            pCenter.add(component);
        }

        JLabel infoButton;
        if (hasInfo) {
            infoButton = createHelpLabel(info);
        } else {
            infoButton = new JLabel();
        }
        pCenter.add(infoButton);
    }

    /**
     * @param elements
     * @param validator
     * @param <T>
     * @return
     */
    protected <T> JComboBox<T> createSelection(T[] elements, Validator<T> validator) {
        JComboBox<T> comboBox = new JComboBox<>(elements);
        comboBox.addActionListener(e -> {
            try {
                if (validator != null) {
                    validator.validate((T) comboBox.getSelectedItem());
                }
                demarkComponentAsErrornous(comboBox);
            } catch (Exception ex) {
                markComponentAsErrornous(comboBox, ex.getMessage());
            }
        });
        return comboBox;

    }


    /**
     * @param title
     * @param info
     * @param value
     * @param validator
     * @return
     */
    protected JCheckBox addCheckBox(String title, String info, boolean value,
            final Validator<Boolean> validator) {
        JCheckBox checkBox = createCheckBox(title, value, validator);
        addRowWithHelp(info, new JLabel(), checkBox);
        return checkBox;
    }


    /**
     * @param title
     * @param file
     * @param info
     * @param isSave
     * @param validator
     * @return
     */
    protected JTextField addFileChooserPanel(String title, String file, String info, boolean isSave,
            final Validator<String> validator) {
        JTextField textField = new JTextField(file);
        textField.addActionListener(e -> {
            try {
                if (validator != null) {
                    validator.validate(textField.getText());
                }
                demarkComponentAsErrornous(textField);
            } catch (Exception ex) {
                markComponentAsErrornous(textField, ex.getMessage());
            }
        });
        JLabel lbl = new JLabel(title);
        lbl.setLabelFor(textField);
        pCenter.add(lbl);
        Box box = new Box(BoxLayout.X_AXIS);
        JButton btnFileChooser = new JButton(IconFontSwing.buildIcon(FontAwesomeSolid.SEARCH, 12f));
        /*
         * btnFileChooser.setBorderPainted(false); btnFileChooser.setFocusPainted(false);
         * btnFileChooser.setContentAreaFilled(false);
         */

        btnFileChooser.addActionListener(e -> {
            KeYFileChooser fileChooser;
            int result;
            if (isSave) {
                fileChooser = KeYFileChooser.getFileChooser("Save file");
                fileChooser.setFileFilter(fileChooser.getAcceptAllFileFilter());
                result = fileChooser.showSaveDialog((Component) e.getSource(),
                    new File(textField.getText()));
            } else {
                fileChooser = KeYFileChooser.getFileChooser("Open file");
                fileChooser.setFileFilter(fileChooser.getAcceptAllFileFilter());
                result = fileChooser.showOpenDialog((Component) e.getSource());
            }
            if (result == JFileChooser.APPROVE_OPTION) {
                textField.setText(fileChooser.getSelectedFile().getAbsolutePath());
            }
        });
        pCenter.add(box);
        box.add(textField);
        box.add(btnFileChooser);
        pCenter.add(createHelpLabel(info), new CC().wrap());
        return textField;
    }

    /**
     * @param title label of the combo box
     * @param info help text
     * @param selectionIndex which item to initially select
     * @param validator validator
     * @param items the items
     * @param <T> the type of the items
     * @return the combo box
     */
    protected <T> JComboBox<T> addComboBox(String title, String info, int selectionIndex,
            @Nullable Validator<T> validator, T... items) {
        JComboBox<T> comboBox = new JComboBox<>(items);
        comboBox.setSelectedIndex(selectionIndex);
        comboBox.addActionListener(e -> {
            try {
                if (validator != null) {
                    validator.validate((T) comboBox.getSelectedItem());
                }
                demarkComponentAsErrornous(comboBox);
            } catch (Exception ex) {
                markComponentAsErrornous(comboBox, ex.getMessage());
            }
        });
        if (info != null && !info.isEmpty()) {
            pCenter.add(new JLabel(title));
            pCenter.add(comboBox);
            JLabel infoButton = createHelpLabel(info);
            pCenter.add(infoButton, new CC().wrap());
        } else if (title != null) {
            pCenter.add(new JLabel(title));
            pCenter.add(comboBox, new CC().wrap());
        } else {
            // TODO: this branch seems to always throw an exception
            add(comboBox, new CC().span(2).wrap());
        }
        return comboBox;
    }

    /**
     * @param title
     * @param component
     * @param helpText
     */
    protected void addTitledComponent(String title, JComponent component, String helpText) {
        JLabel label = new JLabel(title);
        label.setLabelFor(component);
        addRowWithHelp(helpText, label, component);
    }


    protected JTextArea addTextArea(String title, String text, String info,
            final Validator<String> validator) {
        JScrollPane field = createTextArea(text, validator);
        addTitledComponent(title, field, info);
        return (JTextArea) field.getViewport().getView();
    }

    protected JTextArea addTextAreaWithoutScroll(String title, String text, String info,
            final Validator<String> validator) {
        JTextArea field = createTextAreaWithoutScroll(text, validator);
        addTitledComponent(title, field, info);
        return field;
    }


    /**
     * @param title
     * @param text
     * @param info
     * @param validator
     * @return
     */
    protected JTextField addTextField(String title, String text, String info,
            final Validator<String> validator) {
        JTextField field = createTextField(text, validator);
        addTitledComponent(title, field, info);
        return field;
    }


    protected JTextField addTextField(String title, String text, String info,
            final Validator<String> validator, JComponent additionalActions) {
        JTextField field = createTextField(text, validator);
        JLabel label = new JLabel(title);
        label.setLabelFor(field);
        addRowWithHelp(info, label, field, additionalActions);
        return field;
    }

    /**
     * Create a titled JSpinner (with additional information) for entering numbers in [min, max].
     * The min and max values have to be comparable (to check min <= value <= max) and min must be a
     * Number to be handled by the JSpinner's SpinnerNumberModel correctly. The Number class of min
     * also determines how the default NumberFormatter used by the JSpinner formats entered Strings
     * (see {@link javax.swing.text.NumberFormatter#stringToValue(String)}).
     *
     * If there are additional restrictions for the entered values, the passed validator can check
     * those. The entered values have to be of a subclass of Number (as this is a number text
     * field), otherwise the Number-Validator will fail.
     *
     * @param title the title of the text field
     * @param min the minimum value that can be entered
     * @param max the maximum value that can be entered
     * @param step the step size used when changing the entered value using the JSpinner's arrow
     *        buttons
     * @param info arbitrary information about the text field
     * @param validator a validator for checking the entered values
     * @return the created JSpinner
     * @param <T> the class of the minimum value
     */
    protected <T extends Number & Comparable<T>> JSpinner addNumberField(String title, T min,
            Comparable<T> max, Number step, String info, final Validator<Number> validator) {
        JSpinner field = createNumberTextField(min, max, step, validator);
        addTitledComponent(title, field, info);
        return field;
    }

    protected void addRadioButtons(String heading, Object[] alternatives, String description) {
        addRadioButtons(heading, Arrays.asList(alternatives), description);
    }

    protected void addRadioButtons(String title, List<?> alternatives, String description) {
        JPanel items = new JPanel(new GridLayout(alternatives.size(), 1));
        ButtonGroup bg = new ButtonGroup();
        for (Object alt : alternatives) {
            JRadioButton radioButton = new JRadioButton(alt.toString());
            radioButton.putClientProperty("object", alt);
            bg.add(radioButton);
            items.add(radioButton);
        }
        addTitledComponent(title, items, description);
    }

    /**
     * Add a separator line with the given title.
     *
     * @param titleText
     */
    protected void addSeparator(String titleText) {
        JPanel pane = new JPanel(new GridBagLayout());
        GridBagConstraints gbc = new GridBagConstraints();
        gbc.gridwidth = GridBagConstraints.REMAINDER;
        gbc.weightx = 1;
        gbc.fill = GridBagConstraints.HORIZONTAL;
        JSeparator sep = new JSeparator(SwingConstants.HORIZONTAL);
        pane.add(sep, gbc);

        Box box = new Box(BoxLayout.X_AXIS);
        box.add(new JLabel(titleText));
        box.add(pane);
        pCenter.add(box, new CC().span().grow().alignX("left"));
    }

    /**
     * Creates an empty validator instance.
     *
     * @param <T> arbitrary
     * @return non-null
     */
    protected <T> Validator<T> emptyValidator() {
        return s -> {
        };
    }
}
