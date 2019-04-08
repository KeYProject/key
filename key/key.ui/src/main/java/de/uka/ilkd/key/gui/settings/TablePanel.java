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
import de.uka.ilkd.key.gui.smt.FileChooserPanel;
import net.miginfocom.layout.CC;
import net.miginfocom.swing.MigLayout;

import javax.swing.*;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import java.awt.*;
import java.awt.event.ActionListener;

/**
 * 2019-04-08, weigl: rewrite to mig layout
 *
 * @author weigl
 */
public abstract class TablePanel extends JPanel {
    protected TablePanel() {
        setLayout(new MigLayout());
    }

    protected JTextArea createInfoArea(String info) {
        JTextArea textArea = new JTextArea(info);
        textArea.setBackground(this.getBackground());
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
            if (i == length - 1 && !hasInfo) {
                add(component, new CC().wrap().span(2));
            } else {
                add(component);
            }
        }

        if (hasInfo) {
            JLabel infoButton = new JLabel(
                    IconFontSwing.buildIcon(FontAwesomeSolid.QUESTION_CIRCLE, 16f));
            infoButton.setToolTipText(info);
            add(infoButton, new CC().wrap());
        }
    }

    protected JCheckBox createCheckBox(String title, boolean value, ActionListener changeListener) {
        JCheckBox checkBox = new JCheckBox(title, value);
        checkBox.addActionListener(changeListener);
        return checkBox;
    }

    protected JCheckBox addCheckBox(String title, String info,
                                    boolean value, ActionListener changeListener) {
        JCheckBox checkBox = createCheckBox(title, value, changeListener);
        addRowWithHelp(info, checkBox);
        return checkBox;
    }


    protected FileChooserPanel addFileChooserPanel(String title, String file, String info,
                                                   boolean selected, boolean enabled,
                                                   ActionListener changeListener) {
        FileChooserPanel fileChooserPanel = new FileChooserPanel(selected, enabled, title, file);
        fileChooserPanel.addActionListener(changeListener);
        setMaximumHeight(fileChooserPanel, fileChooserPanel.getPreferredSize().height);
        addRowWithHelp(info, fileChooserPanel);
        return fileChooserPanel;
    }

    protected <T> JComboBox<T> addComboBox(String info, int selectionIndex,
                                           ActionListener changeListener, T... items) {
        JComboBox<T> comboBox = new JComboBox<T>(items);
        comboBox.setSelectedIndex(selectionIndex);
        comboBox.addActionListener(changeListener);
        addRowWithHelp(info, comboBox);
        return comboBox;
    }

    private void setMaximumHeight(JComponent component, int height) {
        Dimension dim = component.getMaximumSize();
        dim.height = height;
        component.setMaximumSize(dim);
    }

    protected JTextField createTextField(String text, final ActionListener changeListener) {
        JTextField field = new JTextField(text);
        field.getDocument().addDocumentListener(new DocumentListener() {

            @Override
            public void removeUpdate(DocumentEvent e) {
                if (changeListener != null) changeListener.actionPerformed(null);
            }

            @Override
            public void insertUpdate(DocumentEvent e) {
                if (changeListener != null) changeListener.actionPerformed(null);
            }

            @Override
            public void changedUpdate(DocumentEvent e) {
                if (changeListener != null) changeListener.actionPerformed(null);
            }
        });
        return field;
    }

    protected void addTitledComponent(String title, JComponent component, String helpText) {
        JLabel label = new JLabel(title);
        label.setLabelFor(component);
        addRowWithHelp(helpText, label, component);
    }

    protected JTextField addTextField(String title, String text, String info, final ActionListener changeListener) {
        JTextField field = createTextField(text, changeListener);
        addTitledComponent(title, field, info);
        return field;
    }

    protected void addSeparator(String titleText) {
        add(new JLabel(titleText));
        add(new JSeparator(), new CC().span(2).wrap());
    }
}