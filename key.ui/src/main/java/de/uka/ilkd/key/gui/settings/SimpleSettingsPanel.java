/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.settings;


import java.awt.*;
import java.text.Format;
import javax.annotation.Nullable;
import javax.swing.*;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.text.JTextComponent;

import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;

import org.key_project.util.java.StringUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * A simple panel for using inside of the {@link SettingsUi}.
 * <p>
 * This panel provides a header and center pane.
 * <p>
 * The header already contains a two labels {@link #lblHead} and {@link #lblSubhead} with
 * appropriate fonts.
 * <p>
 * The {@link #pCenter} can be used to add create a settings dialog.
 * <p>
 * Holds various factory methods for creating input components which can be validated.
 *
 * @author weigl
 */
public class SimpleSettingsPanel extends JPanel {

    private static final Logger LOGGER = LoggerFactory.getLogger(SimpleSettingsPanel.class);
    private static final ColorSettings.ColorProperty COLOR_ERROR =
        ColorSettings.define("SETTINGS_TEXTFIELD_ERROR",
            "Color for marking errornous textfields in settings dialog", new Color(200, 100, 100));

    protected final Box pNorth = new Box(BoxLayout.Y_AXIS);
    protected final JPanel pCenter = new JPanel();
    protected final JLabel lblHead = new JLabel();
    protected final JLabel lblSubhead = new JLabel();

    protected SimpleSettingsPanel() {
        setLayout(new BorderLayout());

        pNorth.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));
        pNorth.setBackground(Color.WHITE);
        pNorth.setOpaque(true);

        lblHead.setFont(lblHead.getFont().deriveFont(16f).deriveFont(Font.BOLD));
        pNorth.add(lblHead);
        pNorth.add(lblSubhead);
        pNorth.add(new JSeparator());
        add(pNorth, BorderLayout.NORTH);
        JScrollPane scrollPane = new JScrollPane(pCenter);
        scrollPane.getHorizontalScrollBar().setUnitIncrement(10);
        scrollPane.getVerticalScrollBar().setUnitIncrement(10);
        add(scrollPane, BorderLayout.CENTER);
    }

    public void setHeaderText(String text) {
        lblHead.setText(text);
    }

    public void setSubHeaderText(String text) {
        lblSubhead.setText(text);
    }

    protected void demarkComponentAsErrornous(JComponent component) {
        Object col = component.getClientProperty("saved_background_color");
        if (col instanceof Color) {
            component.setBackground((Color) col);
        }
    }

    protected void markComponentAsErrornous(JComponent component, String error) {
        component.putClientProperty("saved_background_color", component.getBackground());
        component.setBackground(COLOR_ERROR.get());
        component.setToolTipText(error);
    }

    protected JCheckBox createCheckBox(String title, boolean value,
            final @Nullable Validator<Boolean> validator) {
        JCheckBox checkBox = new JCheckBox(title, value);
        checkBox.addActionListener(e -> {
            try {
                if (validator != null) {
                    validator.validate(checkBox.isSelected());
                }
                demarkComponentAsErrornous(checkBox);
            } catch (Exception ex) {
                markComponentAsErrornous(checkBox, ex.getMessage());
            }
        });
        return checkBox;
    }

    protected JScrollPane createTextArea(String text, Validator<String> validator) {
        JTextArea area = new JTextArea(text);
        area.setRows(5);
        area.getDocument().addDocumentListener(new DocumentValidatorAdapter(area, validator));
        return new JScrollPane(area);
    }

    protected JTextArea createTextAreaWithoutScroll(String text, Validator<String> validator) {
        JTextArea area = new JTextArea(text);
        area.setRows(5);
        area.getDocument().addDocumentListener(new DocumentValidatorAdapter(area, validator));
        return area;
    }


    protected JTextField createTextField(String text, final @Nullable Validator<String> validator) {
        JTextField field = new JTextField(text);
        field.getDocument().addDocumentListener(new DocumentValidatorAdapter(field, validator));
        return field;
    }

    protected JFormattedTextField createNumberFormattedTextField(Format format,
            final @Nullable Validator<String> validator) {
        JFormattedTextField field = new JFormattedTextField(format);
        field.getDocument().addDocumentListener(new DocumentValidatorAdapter(field, validator));
        return field;
    }

    /**
     * Create a new JSpinner for numbers in [min, max] using the given step size for its arrow
     * buttons. The min and max values have to be comparable and min will be set as the initial
     * value, so it has to be subclassing the Number class, in order to be handled correctly by the
     * SpinnerNumberModel. Note that min will also determine the Number class into which the
     * JSpinner's NumberFormatter will format entered Strings (see
     * {@link javax.swing.text.NumberFormatter#stringToValue(String)}). Entered values have to be
     * Numbers, otherwise the Number-Validator will fail.
     *
     * @param min the minimum value of the JSpinner
     * @param max the maximum value of the JSpinner
     * @param step the step size of the JSpinner
     * @param validator a validator used to check the entered values for additional restrictions
     * @return the created JSpinner
     * @param <T> the class of the minimum value
     */
    protected <T extends Number & Comparable<T>> JSpinner createNumberTextField(T min,
            Comparable<T> max, Number step, final @Nullable Validator<Number> validator) {
        SpinnerModel spinnerModel = new SpinnerNumberModel(min, min, max, step);
        return createNumberTextField(spinnerModel, validator);
    }

    protected JSpinner createNumberTextField(SpinnerModel model,
            final @Nullable Validator<Number> validator) {
        // create a new spinner that delegates background color changes/requests to its TextField
        JSpinner spinner = new JSpinner(model) {
            @Override
            public void setBackground(Color bg) {
                JSpinner.DefaultEditor editor = (JSpinner.DefaultEditor) getEditor();
                editor.getTextField().setBackground(bg);
            }

            @Override
            public Color getBackground() {
                JSpinner.DefaultEditor editor = (JSpinner.DefaultEditor) getEditor();
                return editor.getTextField().getBackground();
            }
        };
        spinner.setBackground(Color.WHITE); // without this, the background would be gray ...
        spinner.addChangeListener(new ValidatorSpinnerAdapter<>(spinner, validator));
        return spinner;
    }

    public static JLabel createHelpLabel(String s) {
        if (s == null || s.isEmpty()) {
            s = "";
        } else {
            String brokenLines = StringUtil.wrapLines(s);
            s = "<html>"
                + brokenLines.replace("<", "&lt;").replace(">", "&gt;").replace("\n", "<br>");
        }

        JLabel infoButton =
            new JLabel(IconFontSwing.buildIcon(FontAwesomeSolid.QUESTION_CIRCLE, 16f));
        infoButton.setToolTipText(s);
        return infoButton;
    }

    @SuppressWarnings("unchecked")
    private class ValidatorSpinnerAdapter<T> implements ChangeListener {
        private final Validator<T> validator;
        private final JSpinner model;

        public ValidatorSpinnerAdapter(JSpinner model, Validator<T> validator) {
            this.model = model;
            this.validator = validator;
        }

        @Override
        public void stateChanged(ChangeEvent e) {
            Object current = model.getValue();
            try {
                if (validator != null) {
                    // This typecast will lead to an exception if the model's value is not of
                    // (a subclass of) class T.
                    validator.validate((T) current);
                }
                demarkComponentAsErrornous(model);
            } catch (Exception ex) {
                LOGGER.error(ex.getMessage());
                markComponentAsErrornous(model, ex.getMessage());
            }
        }
    }

    private class DocumentValidatorAdapter implements DocumentListener {
        private final JTextComponent field;
        private final @Nullable Validator<String> validator;

        private DocumentValidatorAdapter(JTextComponent field,
                @Nullable Validator<String> validator) {
            this.field = field;
            this.validator = validator;
        }

        @Override
        public void removeUpdate(DocumentEvent e) {
            update();
        }

        @Override
        public void insertUpdate(DocumentEvent e) {
            update();
        }

        @Override
        public void changedUpdate(DocumentEvent e) {
            update();
        }

        void update() {
            try {
                if (validator != null) {
                    validator.validate(field.getText());
                }
                demarkComponentAsErrornous(field);
            } catch (Exception ex) {
                markComponentAsErrornous(field, ex.getMessage());
            }
        }
    }
}
