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
import net.miginfocom.layout.AC;
import net.miginfocom.layout.CC;
import net.miginfocom.layout.LC;
import net.miginfocom.swing.MigLayout;

import javax.swing.*;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import java.awt.*;
import java.text.Format;

/**
 * A panel used inside the settings dialog.
 * <p>
 * Allows a simple building of the UI by defining several factory methods.
 * <p>
 * Uses a three-column miglayout layout.
 * <p>
 * 2019-04-08, weigl: rewrite to mig layout
 *
 * @author weigl
 */
public abstract class SettingsPanel extends SimpleSettingsPanel {
    protected SettingsPanel() {
        pCenter.setLayout(new MigLayout(
                new LC().fillX().wrapAfter(3),
                new AC().count(3).fill(1)
                        .sizeGroup()
                        .size("16px", 2)
                        .grow(0f, 0)
                        .grow(1000f, 1)
                        .align("right", 0)));
    }

    protected static JTextArea createInfoArea(String info) {
        JTextArea textArea = new JTextArea(info);
        //textArea.setBackground(this.getBackground());
        textArea.setEditable(false);
        textArea.setLineWrap(true);
        textArea.setWrapStyleWord(true);
        return textArea;
    }

    protected void addRowWithHelp(String info, JComponent... components) {
        boolean hasInfo = info != null && !info.isEmpty();
        for (int i = 0, length = components.length; i < length; i++) {
            JComponent component = components[i];
            component.setAlignmentX(LEFT_ALIGNMENT);
            //last component, either line break or info
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


    protected JCheckBox addCheckBox(String title, String info,
                                    boolean value, final Validator<Boolean> validator) {
        JCheckBox checkBox = createCheckBox(title, value, validator);
        addRowWithHelp(info, new JLabel(), checkBox);
        return checkBox;
    }


    protected JTextField addFileChooserPanel(String title, String file, String info,
                                             boolean isSave, final Validator<String> validator) {
        JTextField textField = new JTextField(file);
        textField.addActionListener(e -> {
            try {
                validator.validate(textField.getText());
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
        /*btnFileChooser.setBorderPainted(false);
        btnFileChooser.setFocusPainted(false);
        btnFileChooser.setContentAreaFilled(false);*/

        btnFileChooser.addActionListener(e -> {
            JFileChooser f = new JFileChooser(textField.getText());
            int c = 0;
            if (isSave)
                c = f.showSaveDialog((Component) e.getSource());
            else
                c = f.showOpenDialog((Component) e.getSource());
            if (c == JFileChooser.APPROVE_OPTION) {
                textField.setText(f.getSelectedFile().getAbsolutePath());
            }
        });
        pCenter.add(box);
        box.add(textField);
        box.add(btnFileChooser);
        pCenter.add(createHelpLabel(info), new CC().wrap());
        return textField;
    }

    protected <T> JComboBox<T> addComboBox(String info, int selectionIndex,
                                           final Validator<T> validator, T... items) {
        JComboBox<T> comboBox = new JComboBox<>(items);
        comboBox.setSelectedIndex(selectionIndex);
        comboBox.addActionListener(e -> {
            try {
                validator.validate((T) comboBox.getSelectedItem());
                demarkComponentAsErrornous(comboBox);
            } catch (Exception ex) {
                markComponentAsErrornous(comboBox, ex.getMessage());
            }
        });
        if (info != null && !info.isEmpty()) {
            add(new JLabel());
            pCenter.add(comboBox);
            JLabel infoButton = createHelpLabel(info);
            pCenter.add(infoButton, new CC().wrap());
        } else {
            add(comboBox, new CC().span(2).wrap());
        }
        return comboBox;
    }


    protected void addTitledComponent(String title, JComponent component, String helpText) {
        JLabel label = new JLabel(title);
        label.setLabelFor(component);
        addRowWithHelp(helpText, label, component);
    }

    protected JTextField addTextField(String title, String text, String info, final Validator<String> validator) {
        JTextField field = createTextField(text, validator);
        addTitledComponent(title, field, info);
        return field;
    }

    protected JSpinner addNumberField(String title, int min, int max, int step, String info,
                                      final Validator<Integer> validator) {
        JSpinner field = createNumberTextField(min, max, step, validator);
        addTitledComponent(title, field, info);
        return field;
    }

    protected void addSeparator(String titleText) {
        JPanel pane = new JPanel(new GridBagLayout());
        GridBagConstraints gbc = new GridBagConstraints();
        gbc.gridwidth = GridBagConstraints.REMAINDER;
        gbc.weightx = 1;
        gbc.fill = GridBagConstraints.HORIZONTAL;
        JSeparator sep = new JSeparator(JSeparator.HORIZONTAL);
        pane.add(sep, gbc);

        Box box = new Box(BoxLayout.X_AXIS);
        box.add(new JLabel(titleText));
        box.add(pane);
        pCenter.add(box, new CC().span().grow().alignX("left"));
    }

    protected <T> Validator<T> emptyValidator() {
        return s -> {};
    }
}
