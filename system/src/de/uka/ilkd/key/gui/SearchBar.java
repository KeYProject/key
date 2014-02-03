// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui;

import java.awt.Color;
import java.awt.Font;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JTextField;
import javax.swing.KeyStroke;
import javax.swing.border.Border;
import javax.swing.border.CompoundBorder;
import javax.swing.border.EmptyBorder;
import javax.swing.border.LineBorder;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;

/*
 * Abstract parent class of SequentSearchBar and ProofTreeSearchPanel.
 * Might be used for additional search bars.
 */
public abstract class SearchBar extends JPanel {

    public JTextField searchField = new JTextField(20);
    private JButton prev;
    private JButton next;
    private JButton close;
    private final Color ALLERT_COLOR = new Color(255, 178, 178);

    public SearchBar() {
        prev = new JButton(IconFactory.previous(16));
        next = new JButton(IconFactory.next(16));
        close = new JButton(IconFactory.stop(16));

        // Initialize the Actionlisteners here:

        close.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent actionEvent) {
                setVisible(false);
            }
        });

        next.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent actionEvent) {
                searchNext();
                searchField.requestFocusInWindow();
            }
        });

        prev.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent actionEvent) {
                searchPrevious();
                searchField.requestFocusInWindow();
            }
        });

        searchField.registerKeyboardAction(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                searchNext();
            }
        }, KeyStroke.getKeyStroke(KeyEvent.VK_ENTER, 0), JComponent.WHEN_FOCUSED);

        registerKeyboardAction(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                setVisible(false);
            }
        }, KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0), JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);

        searchField.getDocument()
                .addDocumentListener(new DocumentListener() {
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
        Border border = new CompoundBorder(
                new LineBorder(Color.GRAY, 1),
                new EmptyBorder(insets));
        
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

    /* The boolean return value of this function indicates,
     * whether search was successful or not.
     */
    public abstract boolean search(String s);

    public void search() {
        boolean b = search(searchField.getText());
        if (b) {
            searchField.setBackground(Color.WHITE);
        } else {
            searchField.setBackground(ALLERT_COLOR);
        }
    }

    /* Override this method in case you want a custom UI
     * for the search bar.
     */
    public void createUI() {
        setLayout(new BoxLayout(this, BoxLayout.LINE_AXIS));
        add(new JLabel("Search: "));
        add(searchField);
        add(prev);
        prev.setMargin(new java.awt.Insets(2,1,2,1));
        add(next);
        next.setMargin(new java.awt.Insets(2,1,2,1));
        add(close);
        close.setMargin(new java.awt.Insets(2,1,2,1));
    }
}
