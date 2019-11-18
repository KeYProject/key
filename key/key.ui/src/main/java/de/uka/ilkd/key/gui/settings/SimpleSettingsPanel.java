// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.settings;


import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;

import javax.swing.*;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import java.awt.*;
import java.text.Format;

/**
 * A simple panel for using inside of the {@link SettingsUi}.
 * <p>
 * This panel provides a header and center pane.
 * <p>
 * The header already contains a two labels {@link #lblHead} and {@link #lblSubhead} with appropriate fonts.
 * <p>
 * The {@link #pCenter} can be used to add create a settings dialog.
 * <p>
 * Holds various factory methods for creating input components which can be validated.
 *
 * @author weigl
 */
public class SimpleSettingsPanel extends JPanel {
    private static final long serialVersionUID = -6727362750311983463L;
    protected Box pNorth = new Box(BoxLayout.Y_AXIS);
    protected JPanel pCenter = new JPanel();
    protected JLabel lblHead = new JLabel();
    protected JLabel lblSubhead = new JLabel();

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
        add(pCenter, BorderLayout.CENTER);
    }

    public void setHeaderText(String text) {
        lblHead.setText(text);
    }

    public void setSubHeaderText(String text) {
        lblSubhead.setText(text);
    }

    protected void demarkComponentAsErrornous(JComponent component) {
        component.setBackground(Color.white);//find color
    }

    protected void markComponentAsErrornous(JComponent component, String error) {
        component.setBackground(Color.RED);
        component.setToolTipText(error);
    }

    protected JCheckBox createCheckBox(String title, boolean value, final Validator<Boolean> validator) {
        JCheckBox checkBox = new JCheckBox(title, value);
        checkBox.addActionListener(e -> {
            try {
                validator.validate(checkBox.isSelected());
                demarkComponentAsErrornous(checkBox);
            } catch (Exception ex) {
                markComponentAsErrornous(checkBox, ex.getMessage());
            }
        });
        return checkBox;
    }

    protected JTextField createTextField(String text, final Validator<String> validator) {
        JTextField field = new JTextField(text);
        field.getDocument().addDocumentListener(new DocumentValidatorAdapter(field, validator));
        return field;
    }

    protected JFormattedTextField createNumberFormattedTextField(Format format, final Validator<String> validator) {
        JFormattedTextField field = new JFormattedTextField(format);
        field.getDocument().addDocumentListener(new DocumentValidatorAdapter(field, validator));
        return field;
    }

    protected JSpinner createNumberTextField(int min, int max, int step, final Validator<Integer> validator) {
        SpinnerModel spinnerModel = new SpinnerNumberModel(min, min, max, step);
        return createNumberTextField(spinnerModel, validator);
    }

    protected <T> JSpinner createNumberTextField(SpinnerModel model, final Validator<T> validator) {
        JSpinner field = new JSpinner(model);
        field.addChangeListener(new ValidatorSpinnerAdapter<>(field, validator));
        return field;
    }

    public static JLabel createHelpLabel(String s) {
        if (s == null || s.isEmpty())
            s = "";
        else
            s = "<html>" + s.replaceAll("\n", "<br>");
        JLabel infoButton = new JLabel(
                IconFontSwing.buildIcon(FontAwesomeSolid.QUESTION_CIRCLE, 16f));
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
                validator.validate((T) current);
                demarkComponentAsErrornous(model);
            } catch (Exception ex) {
                markComponentAsErrornous(model, ex.getMessage());
            }
        }
    }

    private class DocumentValidatorAdapter implements DocumentListener {
        private final JTextField field;
        private final Validator<String> validator;

        private DocumentValidatorAdapter(JTextField field, Validator<String> validator) {
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
                validator.validate(field.getText());
                demarkComponentAsErrornous(field);
            } catch (Exception ex) {
                markComponentAsErrornous(field, ex.getMessage());
            }
        }
    }
}
