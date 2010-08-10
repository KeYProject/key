// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.Color;
import java.awt.event.FocusEvent;
import java.awt.event.FocusListener;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.regex.PatternSyntaxException;

import javax.swing.JComponent;

import de.uka.ilkd.key.gui.IMain;
import de.uka.ilkd.key.pp.Range;

/**
 * Implements an incremental search for the sequent view. The incremental search
 * starts with <code>/</code> and is aborted if the sequent view looses the
 * focus or the key <code>Esc</code> is pressed. The next match can be found
 * pressing the function key <code>F3</code>.
 * 
 */
public class IncrementalSearch implements KeyListener, FocusListener {

    private int         startPos;

    private String      searchStr;

    private Object      searchHighlight;

    private SequentView seqView;

    private IMain        main;

    /**
     * create and initialize a new incremental search run
     * 
     * @param seqView
     *            the SequentView where to perform an incremental search
     */
    public IncrementalSearch(SequentView seqView) {

        if (alreadyRegistered(seqView)) {
            return;
        }

        this.seqView = seqView;

        init();

        if (seqView.mediator().mainFrame() instanceof IMain) {
            main = (IMain) seqView.mediator().mainFrame();
        }

        printStatus("Search: " + searchStr);

    }

    /**
     * checks if an incremental search is already taken place at the specified
     * sequent view
     * 
     * @param comp
     *            the JComponent to be checked
     * @return true if incremental search has been already activated for the
     *         component
     */
    private boolean alreadyRegistered(JComponent comp) {
        KeyListener[] l = comp.getKeyListeners();
        for (KeyListener aL : l) {
            if (aL instanceof IncrementalSearch) {
                return true;
            }
        }
        return false;
    }

    /**
     * initialises the incremental search
     */
    private void init() {
        searchStr = "";
        startPos = seqView.getCaret().getMark();
        searchHighlight = seqView.getColorHighlight(Color.RED);

        seqView.addKeyListener(this);
        seqView.addFocusListener(this);
    }

    /**
     * disable this searcher
     */
    private void disableSearchMode() {
        seqView.removeKeyListener(this);
        seqView.removeFocusListener(this);
        seqView.removeHighlight(searchHighlight);

        searchStr = "";
        startPos = 0;

        if (main != null) {
            main.setStandardStatusLine();
        }
    }

    /**
     * disables the incremental searcher when the function key <code>F3</code>
     * is pressed
     */
    public void keyPressed(KeyEvent e) {
        if (e.getKeyCode() == KeyEvent.VK_F3) {
            startPos = startPos + 1;
            seqView.setCaretPosition(startPos);
            searchPattern();
        }
    }

    /**
     * does nothing
     */
    public void keyReleased(KeyEvent e) {
    }

    /**
     * constructs the string to serach for
     */
    public void keyTyped(KeyEvent e) {
        final char ch = e.getKeyChar();
        switch (ch) {
        case KeyEvent.VK_ESCAPE:
            disableSearchMode();
            return;
        case KeyEvent.VK_BACK_SPACE:
            if (searchStr.length() > 1) {
                searchStr = searchStr.substring(0, searchStr.length() - 1);
            } else {
                disableSearchMode();
                return;
            }
            break;
        default:
            searchStr += ch;
            break;
        }
        searchPattern();
    }

    /**
     * searches for the occurence of the specified string
     */
    private void searchPattern() {
       
        String escaped = searchStr.replaceAll
            ("([\\+ | \\* | \\| | \\\\ | \\[ | \\] | \\{ | \\} | \\( | \\)])", 
            "\\\\$1");       
            
        seqView.disableHighlights();

        int caseInsensitiveFlag = 0;

        // no capital letters used --> case insensitive matching
        if (searchStr.toLowerCase().equals(searchStr)) {
            caseInsensitiveFlag = Pattern.CASE_INSENSITIVE;
        }

        
        Pattern p;
        try { 
            p = Pattern.compile(escaped, caseInsensitiveFlag);
        } catch (PatternSyntaxException pse) {           
            return;
        } catch (IllegalArgumentException iae) {
            return;
        }
        
        Matcher m = p.matcher(seqView.getText());

        String status = "Search: " + searchStr;

        if (m.find(startPos)) {
            int foundAt = m.start();
            startPos = foundAt;
            seqView.setCaretPosition(foundAt);
            seqView.paintHighlight(new Range(foundAt, foundAt
                    + searchStr.length()), searchHighlight);
        } else {
            startPos = 0;
            status += " (not found)";
        }

        printStatus(status);
    }

    /**
     * prints the given String in the statusline
     */
    private void printStatus(String text) {
        if (main != null) {
            main.setStatusLine(text);
        }
    }

    // the methods below implement the focus listener
    // incremental search is aborted if the sequent view has no
    // longer the focus

    public void focusGained(FocusEvent e) {

    }

    /**
     * aborts incremental search, if the observed component looses the focus
     */
    public void focusLost(FocusEvent e) {
        disableSearchMode();
        seqView.removeFocusListener(this);
    }
}
