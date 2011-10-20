// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.Color;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.regex.PatternSyntaxException;


import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.util.Pair;
import java.awt.BorderLayout;
import java.awt.Container;
import java.awt.Dimension;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.util.ArrayList;
import java.util.List;
import javax.swing.JCheckBox;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JTextField;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;

/**
 * Implements an incremental search for the sequent view. The incremental search
 * starts with <code>/</code> and is aborted if the sequent view looses the
 * focus or the key <code>Esc</code> is pressed. The next match can be found
 * pressing the function key <code>F3</code>.
 * 
 */
public class IncrementalSearch {

    public static final Color SEARCH_HIGHLIGHT_COLOR_1 =
            new Color(255, 140, 0, 178);
    public static final Color SEARCH_HIGHLIGHT_COLOR_2 =
            new Color(255, 140, 0, 76);


    private static IncrementalSearch instance = new IncrementalSearch();

    private final DocumentListenerAdapter documentListenerAdapter;

    private String searchStr;
    private List<Pair<Integer,Object>> searchResults;
    private int resultIteratorPos;

    private SequentView seqView;
    private SearchDialog searchDialog;

    private boolean regExpSearch;

    /**
     * create and initialize a new incremental search run
     * 
     * @param seqView
     *            the SequentView where to perform an incremental search
     */
    private IncrementalSearch() {
        seqView = null;
        searchStr = "";
        searchResults = new ArrayList<Pair<Integer,Object>>();
        documentListenerAdapter = new DocumentListenerAdapter();
        regExpSearch = false;
        searchDialog = new SearchDialog();
        searchDialog.addKeyListener(new KeyListener() {

            @Override
            public void keyTyped(KeyEvent e) {
                final char ch = e.getKeyChar();
                switch (ch) {
                case KeyEvent.VK_ESCAPE:
                    disableSearch();
                    return;
                case KeyEvent.VK_ENTER:
                    highlightNext();
                    return;
                }
            }

            @Override
            public void keyPressed(KeyEvent e) {
                if (e.isShiftDown() && e.getKeyCode() == KeyEvent.VK_F3) {
                    highlightPrev();
                } else if (e.getKeyCode() == KeyEvent.VK_F3) {
                    highlightNext();
                }
            }

            @Override
            public void keyReleased(KeyEvent e) {
            }

        });
        searchDialog.addDocumentListener(documentListenerAdapter);
    }

    
    public static IncrementalSearch getInstance(){
        return instance;
    }


    public void highlightNext() {
        if (!searchResults.isEmpty()) {
            resetExtraHighlight();
            resultIteratorPos = (resultIteratorPos + 1) % searchResults.size();
            setExtraHighlight(resultIteratorPos);
        }
    }


    public void highlightPrev() {
        if (!searchResults.isEmpty()) {
            resetExtraHighlight();
            resultIteratorPos =
                    (resultIteratorPos - 1 + searchResults.size()) %
                    searchResults.size();
            setExtraHighlight(resultIteratorPos);
        }
    }

    
    public void initSearch(SequentView seqView) {
        if (seqView == null || this.seqView == seqView) {
            return;
        } else if (this.seqView != null) {
            disableSearch();
        }
        this.seqView = seqView;
        this.seqView.getDocument().addDocumentListener(documentListenerAdapter);
        searchDialog.setVisible(true);
        searchPattern();
    }


    /**
     * disable this searcher
     */
    public void disableSearch() {
        searchDialog.setVisible(false);
        if (seqView != null) {
            clearSearchResults();
            seqView.getDocument().removeDocumentListener(documentListenerAdapter);
            seqView = null;
        }
    }


    private void clearSearchResults() {
        for (Pair result : searchResults) {
            seqView.removeHighlight(result.second);
        }
        searchResults.clear();
    }


    public boolean isInitialised() {
        return seqView != null;
    }


    /**
     * searches for the occurence of the specified string
     */
    public void searchPattern() {
        clearSearchResults();

        if (seqView == null || seqView.getText() == null || searchStr.equals("")) {
            searchDialog.deactivateAllertColor();
            return;
        }

        searchResults.clear();
        resultIteratorPos = 0;

        int searchFlag = 0;
        if (searchStr.toLowerCase().equals(searchStr)) {
            // no capital letters used --> case insensitive matching
            searchFlag = searchFlag | Pattern.CASE_INSENSITIVE
                    | Pattern.UNICODE_CASE;
        }
        if (!regExpSearch) {
            // search for literal string instead of regExp
            searchFlag = searchFlag | Pattern.LITERAL;
        }

        Pattern p;
        try {
            p = Pattern.compile(searchStr, searchFlag);
        } catch (PatternSyntaxException pse) {
            searchDialog.activateAllertColor();
            return;
        } catch (IllegalArgumentException iae) {
            searchDialog.activateAllertColor();
            return;
        }
        Matcher m = p.matcher(seqView.getText());

        boolean loopEnterd = false;
        while (m.find()) {
                int foundAt = m.start();
                Object highlight = seqView.getColorHighlight(SEARCH_HIGHLIGHT_COLOR_2);
                searchResults.add(new Pair<Integer,Object>(foundAt, highlight));
                seqView.paintHighlight(new Range(foundAt, m.end()), highlight);
                loopEnterd = true;
        }
        if (loopEnterd) {
            seqView.updateUpdateHighlights();
            searchDialog.deactivateAllertColor();
        } else {
            searchDialog.activateAllertColor();
        }
    }

    
    private void setExtraHighlight(int resultIndex) {
        resetHighlight(resultIndex,
                       seqView.getColorHighlight(SEARCH_HIGHLIGHT_COLOR_1));
        seqView.setCaretPosition(searchResults.get(resultIndex).first);
    }


    private void resetExtraHighlight() {
        resetHighlight(resultIteratorPos,
                       seqView.getColorHighlight(SEARCH_HIGHLIGHT_COLOR_2));
    }


    private void resetHighlight(int resultIndex, Object highlight) {
        int pos = searchResults.get(resultIndex).first;
        seqView.removeHighlight(searchResults.get(resultIndex).second);
        Pair<Integer, Object> highlightPair =
                new Pair<Integer, Object>(pos, highlight);
        seqView.paintHighlight(new Range(pos, pos + searchStr.length()), highlight);
        seqView.updateUpdateHighlights();
        searchResults.set(resultIndex, highlightPair);
    }


    public void requestFocus() {
        searchDialog.requestFocus();
    }


    public void setRegExpSearch(boolean b) {
        regExpSearch = b;
        searchPattern();
    }


    

    private class SearchDialog extends JDialog {
        /**
         * 
         */
        private static final long serialVersionUID = -6940680783649580399L;
        public final Color ALLERT_COLOR = new Color(255, 178, 178);
        public final Dimension INIT_SIZE =
                new JDialog().getContentPane().add(new JTextField("12345678901234567890")).getPreferredSize();
        
        private JTextField textField;


        public SearchDialog() {
            super((JDialog)null, "Search", false);
            getContentPane().setLayout(new BorderLayout());
            getContentPane().add(initTextField(), BorderLayout.CENTER);
            getContentPane().add(initRegExpCheckbox(), BorderLayout.EAST);
            setAlwaysOnTop(true);
            addWindowListener(new WindowAdapter() {
                public void windowClosing(WindowEvent e) {
                    disableSearch();
                }
            });
        }

        private JComponent initTextField() {
            textField = new JTextField();
            textField.setPreferredSize(INIT_SIZE);
            textField.setToolTipText("<html>"
                                     + "This search dialog features "
                                     + "<b>drag'n'drop</b> and "
                                     + "<b>copy'n'paste</b>.<br>"
                                     + "Further more the following shurtcuts "
                                     + "can be used:<br>"
                                     + "<b>ENTER</b> or <b>F3</b>: "
                                     + "highlight next occurrence<br>"
                                     + "<b>SHIFT F3</b>: "
                                     + "highlight previous occurrence<br>"
                                     + "<b>ESC</b>: disable search"
                                     + "</html>");
            return textField;
        }

        private JComponent initRegExpCheckbox() {
            JCheckBox checkBox = new JCheckBox("RegExp");
            checkBox.addItemListener(new ItemListener() {
                @Override
                public void itemStateChanged(ItemEvent e) {
                    regExpCheckBoxChanged((JCheckBox)e.getItemSelectable());
                }
            });
            checkBox.setSelected(regExpSearch);
            return checkBox;
        }


        @Override
        public void addKeyListener(KeyListener l) {
            textField.addKeyListener(l);
        }


        public void addDocumentListener(DocumentListener l) {
            textField.getDocument().addDocumentListener(l);
        }

        
        @Override
        public void requestFocus() {
            textField.requestFocus();
        }


        public String getText() {
            return textField.getText();
        }


        public void activateAllertColor() {
            textField.setBackground(ALLERT_COLOR);
        }


        public void deactivateAllertColor() {
            textField.setBackground(Color.WHITE);
        }


        private void regExpCheckBoxChanged(JCheckBox regExpBox) {
            setRegExpSearch(regExpBox.isSelected());
        }


        @Override
        public void setVisible(boolean b) {
            if (seqView != null
                    && seqView.getParent() != null
                    && seqView.getParent().getBounds() != null) {
                Container parent = seqView.getParent();
                // dimension of scroll pane minus frame dimension
                int x = parent.getBounds().width - INIT_SIZE.width;
                int y = parent.getBounds().height - INIT_SIZE.height;
                // plus parent positions
                parent = parent.getParent();
                while (parent != null) {
                    x += parent.getBounds().x;
                    y += parent.getBounds().y;
                    parent = parent.getParent();
                }
                setLocation(x, y);
                pack();
            }
            super.setVisible(b);
        }
    }


    private class DocumentListenerAdapter implements DocumentListener {

        @Override
        public void insertUpdate(DocumentEvent e) {
            searchStr = searchDialog.getText();
            searchPattern();
        }


        @Override
        public void removeUpdate(DocumentEvent e) {
            searchStr = searchDialog.getText();
            searchPattern();
        }


        @Override
        public void changedUpdate(DocumentEvent e) {
            searchStr = searchDialog.getText();
            searchPattern();
        }
    }
}
