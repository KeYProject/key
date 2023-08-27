/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.KeyEvent;
import javax.annotation.Nonnull;
import javax.swing.*;
import javax.swing.border.Border;
import javax.swing.border.CompoundBorder;
import javax.swing.border.EmptyBorder;
import javax.swing.border.LineBorder;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;

import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.gui.fonticons.IconFactory;

/*
 * Abstract parent class of SequentSearchBar and ProofTreeSearchPanel. Might be used for additional
 * search bars.
 */
public abstract class SearchBar extends JPanel {

    /**
     *
     */
    private static final long serialVersionUID = -4821960226273983607L;
    public final JTextField searchField = new JTextField(20);
    private final JButton prev;
    private final JButton next;
    private final JButton close;
    private final ColorSettings.ColorProperty ALERT_COLOR =
        ColorSettings.define("[searchBar]alert", "", new Color(255, 178, 178));

    public SearchBar() {
        prev = new JButton(IconFactory.previous(16));
        next = new JButton(IconFactory.next(16));
        close = new JButton(IconFactory.close(16));

        // Initialize the Actionlisteners here:

        close.addActionListener(actionEvent -> setVisible(false));

        next.addActionListener(actionEvent -> {
            searchNext();
            searchField.requestFocusInWindow();
        });

        prev.addActionListener(actionEvent -> {
            searchPrevious();
            searchField.requestFocusInWindow();
        });

        searchField.registerKeyboardAction(e -> searchNext(),
            KeyStroke.getKeyStroke(KeyEvent.VK_ENTER, 0), JComponent.WHEN_FOCUSED);

        registerKeyboardAction(e -> setVisible(false),
            KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0),
            JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);

        searchField.getDocument().addDocumentListener(new DocumentListener() {
            public void changedUpdate(DocumentEvent e) {
                search();
            }

            public void insertUpdate(DocumentEvent e) {
                search();
            }

            public void removeUpdate(DocumentEvent e) {
                search();
            }
        });

        // prepare search buttons

        Font font = prev.getFont().deriveFont(20.0f);
        prev.setFont(font);
        next.setFont(font);
        close.setFont(font);

        prev.setToolTipText("Jump to previous match");
        next.setToolTipText("Jump to next match");
        close.setToolTipText("Close search bar");

        Insets insets = new Insets(0, 4, 0, 4);
        Border border = new CompoundBorder(new LineBorder(Color.GRAY, 1), new EmptyBorder(insets));

        prev.setBorder(border);
        next.setBorder(border);
        close.setBorder(border);

        createUI();
        setVisible(false);
    }

    @Override
    public void setVisible(boolean vis) {
        super.setVisible(vis);
        if (vis) {
            searchField.selectAll();
            searchField.requestFocus();
        }
    }

    public abstract void searchPrevious();

    public abstract void searchNext();

    /*
     * The boolean return value of this function indicates, whether search was successful or not.
     */
    public abstract boolean search(@Nonnull String s);

    public void search() {
        boolean match = search(searchField.getText());
        if (match) {
            searchField.setBackground(Color.WHITE);
        } else {
            searchField.setBackground(ALERT_COLOR.get());
        }
    }

    /*
     * Override this method in case you want a custom UI for the search bar.
     */
    public void createUI() {
        setLayout(new BoxLayout(this, BoxLayout.LINE_AXIS));
        add(new JLabel("Search: "));
        add(searchField);
        add(prev);
        prev.setMargin(new java.awt.Insets(2, 1, 2, 1));
        add(next);
        next.setMargin(new java.awt.Insets(2, 1, 2, 1));
        add(close);
        close.setMargin(new java.awt.Insets(2, 1, 2, 1));
    }
}
