/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.gui;

import java.awt.*;
import java.util.Collection;
import javax.swing.*;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.text.Element;

import de.uka.ilkd.key.gui.configuration.Config;

import org.key_project.util.java.StringUtil;


/**
 * The information window is used to present detailed information about the execution of a solver.
 * In particular it presents information about: - the concrete translation that was passed to the
 * solver - the translation of the taclets - the messages that were sent between KeY and the
 * external solvers.
 * <p>
 * Adaptation of {@link de.uka.ilkd.key.gui.smt.InformationWindow} for Isabelle solvers
 */
public class InformationWindow extends JDialog {
    public record Information(String title, String content, String solver) {
    }

    private JTabbedPane tabbedPane;

    public InformationWindow(Dialog parent, Collection<Information> information,
            String title) {
        super(parent);
        this.setTitle(title);
        for (Information el : information) {
            getTabbedPane().addTab(el.title, newTab(el));
        }

        setSize(600, 500);
        this.getContentPane().add(getTabbedPane());
        this.setModalExclusionType(ModalExclusionType.APPLICATION_EXCLUDE);
        this.setDefaultCloseOperation(DISPOSE_ON_CLOSE);
        this.setLocationRelativeTo(parent);
        this.setVisible(true);
    }

    private Component newTab(Information information) {
        final JTextArea lines = new JTextArea("1");
        final JTextArea content = new JTextArea();
        content.setFont(UIManager.getFont(Config.KEY_FONT_SEQUENT_VIEW));
        lines.setBackground(Color.LIGHT_GRAY);
        lines.setEditable(false);
        content.setEditable(false);

        content.getDocument().addDocumentListener(new DocumentListener() {
            public String getText() {
                int caretPosition = content.getDocument().getLength();
                Element root = content.getDocument().getDefaultRootElement();
                StringBuilder text = new StringBuilder("1" + StringUtil.NEW_LINE);
                for (int i = 2; i < root.getElementIndex(caretPosition) + 2; i++) {
                    text.append(i).append(StringUtil.NEW_LINE);
                }
                return text.toString();
            }

            @Override
            public void changedUpdate(DocumentEvent de) {
                lines.setText(getText());
            }

            @Override
            public void insertUpdate(DocumentEvent de) {
                lines.setText(getText());
            }

            @Override
            public void removeUpdate(DocumentEvent de) {
                lines.setText(getText());
            }
        });
        content.setText(information.content);
        content.setCaretPosition(0);
        JScrollPane pane = new JScrollPane();
        pane.getViewport().add(content);
        pane.setRowHeaderView(lines);
        pane.setVerticalScrollBarPolicy(JScrollPane.VERTICAL_SCROLLBAR_ALWAYS);
        return pane;
    }


    private JTabbedPane getTabbedPane() {
        if (tabbedPane == null) {
            tabbedPane = new JTabbedPane();
        }
        return tabbedPane;
    }
}
