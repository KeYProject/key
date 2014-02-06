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

package de.uka.ilkd.key.gui.utilities;

import java.awt.Color;
import java.awt.Graphics;
import java.awt.Rectangle;
import java.awt.Shape;

import javax.swing.*;
import javax.swing.event.CaretEvent;
import javax.swing.event.CaretListener;
import javax.swing.plaf.TextUI;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter;
import javax.swing.text.Document;
import javax.swing.text.JTextComponent;
import javax.swing.text.Highlighter.HighlightPainter;

/**
 * The Class BracketMatchingTextArea provides a GUI TextArea component which
 * automatically highlights matching pairs of parentheses. It behaves like a
 * {@link JTextArea} object in every other respect.
 *
 * <ul>
 * <li>The following characters are considered as opening parenthesis:
 * <code>( { &lt; [</code>
 * <li>The following characters are considered as closing parenthesis:
 * <code>) } &gt; ]</code>
 * </ul>
 *
 * It is not checked whether the parenthesis are of the same type. Therefore,
 * <code>{x)</code> is highlighted as well.
 *
 * @author mulbrich
 */
public class BracketMatchingTextArea extends JTextArea implements CaretListener {

    /**
     * The Constant serialVersionUID needed for serialisation reasons
     */
    private static final long serialVersionUID = 1649172317561172229L;

    /**
     * The Constant HIGHLIGHT_COLOR holds the color to be used for the highlighting frame, if
     * the matching parentheses are of the same kind
     */
    private static final Color HIGHLIGHT_COLOR_SAME_PARENS = Color.LIGHT_GRAY;

    /**
     * The Constant HIGHLIGHT_COLOR holds the color to be used for the highlighting frame,
     * if the matching parentheses are of different kind.
     */
    private static final Color HIGHLIGHT_COLOR_DIFFERENT_PARENS = Color.RED;

    /**
     * The Constant PAINTER is the painter which is used to draw the highlighting for
     * matching parens of same kind.
     */
    private static final HighlightPainter SAME_PAINTER =
            new BorderPainter(HIGHLIGHT_COLOR_SAME_PARENS);

    /**
     * The Constant PAINTER is the painter which is used to draw the highlighting for
     * matching parens of different kind.
     */
    private static final HighlightPainter DIFF_PAINTER =
            new BorderPainter(HIGHLIGHT_COLOR_DIFFERENT_PARENS);

    /**
     * The Constant OPENING_PARENS holds the characters which serve as opening parenthesis
     */
    private static final String OPENING_PARENS = "({[";

    /**
     * The Constant CLOSING_PARENS holds the characters which serve as closing parenthesis.
     */
    private static final String CLOSING_PARENS = ")}]";

    /**
     * The highlighter stores the highlights in an object which is used to denote the highlighting.
     */
    private Object theSameParensHighlight;

    /**
     * The highlighter stores the highlights in an object which is used to denote the highlighting.
     */
    private Object theDiffParensHighlight;


    /**
     * Constructs a new TextArea.  A default model is set, the initial string
     * is null, and rows/columns are set to 0.
     */
    public BracketMatchingTextArea() {
        super();
        init();
    }

    /**
     * Constructs a new JTextArea with the specified number of rows
     * and columns, and the given model.  All of the constructors
     * feed through this constructor.
     *
     * @param doc the model to use, or create a default one if null
     * @param text the text to be displayed, null if none
     * @param rows the number of rows >= 0
     * @param columns the number of columns >= 0
     * @exception IllegalArgumentException if the rows or columns
     *  arguments are negative.
     */
    public BracketMatchingTextArea(Document doc, String text, int rows,
            int columns) {
        super(doc, text, rows, columns);
        init();
    }

    /**
     * Constructs a new JTextArea with the given document model, and defaults
     * for all of the other arguments (null, 0, 0).
     *
     * @param doc  the model to use
     */
    public BracketMatchingTextArea(Document doc) {
        super(doc);
        init();
    }

    /**
     * Constructs a new empty TextArea with the specified number of
     * rows and columns.  A default model is created, and the initial
     * string is null.
     *
     * @param rows the number of rows >= 0
     * @param columns the number of columns >= 0
     * @exception IllegalArgumentException if the rows or columns
     *  arguments are negative.
     */
    public BracketMatchingTextArea(int rows, int columns) {
        super(rows, columns);
        init();
    }

    /**
     * Constructs a new TextArea with the specified text and number
     * of rows and columns.  A default model is created.
     *
     * @param text the text to be displayed, or null
     * @param rows the number of rows >= 0
     * @param columns the number of columns >= 0
     * @exception IllegalArgumentException if the rows or columns
     *  arguments are negative.
     */
    public BracketMatchingTextArea(String text, int rows, int columns) {
        super(text, rows, columns);
        init();
    }

    /**
     * Constructs a new TextArea with the specified text displayed.
     * A default model is created and rows/columns are set to 0.
     *
     * @param text the text to be displayed, or null
     */
    public BracketMatchingTextArea(String text) {
        super(text);
        init();
    }

    /*
     * Initialize the object. set the highlighting. add listener
     */
    private void init() {
        addCaretListener(this);

        DefaultHighlighter highlight = new DefaultHighlighter();
        // highlight.setDrawsLayeredHighlights(false);
        setHighlighter(highlight);
        try {
            theSameParensHighlight = highlight.addHighlight(0, 0, SAME_PAINTER);
            theDiffParensHighlight = highlight.addHighlight(0, 0, DIFF_PAINTER);
        } catch (BadLocationException e) {
            // may not happen even if document is empty
            throw new Error(e);
        }
    }

    /*
     * check if the caret is on a paren and if so, find the corresponding partner.
     * update the highlighting if such a partner exists.
     */
    public void caretUpdate(CaretEvent e) {
        Object theHighlight = theSameParensHighlight;
        try {
            int dot = getCaretPosition();
            String text = getText();
            char charOn = dot == text.length() ? 0 : text.charAt(dot);
            char charBefore = dot == 0 ? 0 : text.charAt(dot-1);
            int begin = -1;
            int end = -1;

            if(OPENING_PARENS.indexOf(charOn) != -1) {
                end = findMatchingClose(dot);
                if(end > 0)
                    end++;
                begin = dot;
            } else if(CLOSING_PARENS.indexOf(charBefore) != -1) {
                end = dot;
                begin = findMatchingOpen(dot-1);
            }

            if(end != -1 && begin != -1) {
                assert begin < end : "begin=" + begin + " end=" + end;
                assert end > 0;

                if (CLOSING_PARENS.indexOf(text.charAt(end - 1)) !=
                      OPENING_PARENS.indexOf(text.charAt(begin))) {
                    theHighlight = theDiffParensHighlight;
                } else {
                    theHighlight = theSameParensHighlight;
                }

                getHighlighter().changeHighlight(theHighlight, begin, end);
            } else {
                resetHighlights();
            }
        } catch (BadLocationException ex) {
            ex.printStackTrace();
            try {
                resetHighlights();
            } catch (BadLocationException ex2) {
                // may not happen even if document is empty
                throw new Error(ex2);
            }
        }
    }

    /**
     * resets both highlights
     * @throws BadLocationException if the caret is invalid
     */
    protected void resetHighlights() throws BadLocationException {
        getHighlighter().changeHighlight(theSameParensHighlight, 0, 0);
        getHighlighter().changeHighlight(theDiffParensHighlight, 0, 0);
    }

    /**
     * Find matching close paren.
     *
     * Go through the string and find the closing partner. There may be other
     * open/close parens in between
     *
     * @param dot
     *                position to start search from (must be an opening paren)
     * @return either the index of the closing partner or -1 if it does not
     *         exist.
     */
    private int findMatchingClose(int dot) {
        int count = 0;
        String text = getText();

        do {
            if(OPENING_PARENS.indexOf(text.charAt(dot)) != -1)
                count ++;
            else if(CLOSING_PARENS.indexOf(text.charAt(dot)) != -1)
                count --;

            if(count == 0)
                return dot;

            dot ++;
        } while(dot < text.length());
        return -1;
    }

    /**
     * Find matching open paren.
     *
     * Go backward through the string and find the opening partner. There may be
     * other open/close parens in between
     *
     * @param dot
     *                position to start search from (must be a closing paren)
     * @return either the index of the opening partner or -1 if it does not
     *         exist.
     */
    private int findMatchingOpen(int dot) {
        int count = 0;
        String text = getText();

        do {
            if(OPENING_PARENS.indexOf(text.charAt(dot)) != -1)
                count --;
            else if(CLOSING_PARENS.indexOf(text.charAt(dot)) != -1)
                count ++;

            if(count == 0)
                return dot;

            dot --;
        } while(dot >= 0);
        return -1;
    }

    /*
     * for testing
     */
    public static void main(String[] args) {
        JFrame f = new JFrame("Test bracket matching text area");
        f.getContentPane().add(new BracketMatchingTextArea("nothing", 10, 10));
        f.setSize(200, 200);
        f.setVisible(true);
        f.setDefaultCloseOperation(WindowConstants.EXIT_ON_CLOSE);
    }

    /**
     * The Class BorderPainter is a simple highlight painter that just draws a rectangle around the selection.
     *
     */
    static private class BorderPainter implements HighlightPainter {

        private final Color highlightColor;

        public BorderPainter(Color highlightColor) {
            this.highlightColor = highlightColor;
        }

        /**
         * The code is copied from @link DefaultHighlighter#DefaultPainter#paint(Graphics)
         */
        public void paint(Graphics g, int offs0, int offs1, Shape bounds,
                JTextComponent c) {

            // dont render if empty
            if(offs0 == offs1)
                return;

            Rectangle alloc = bounds.getBounds();
            try {
                // --- determine locations ---
                TextUI mapper = c.getUI();
                Rectangle p0 = mapper.modelToView(c, offs0);
                Rectangle p1 = mapper.modelToView(c, offs1);

                g.setColor(highlightColor);

                if (p0.y == p1.y) {
                    // same line, render a rectangle
                    Rectangle r = p0.union(p1);
                    g.drawRect(r.x, r.y, r.width-1, r.height-1);
                } else {
                    // different lines
                    int p0ToMarginWidth = alloc.x + alloc.width - p0.x;
                    g.drawRect(p0.x, p0.y, p0ToMarginWidth, p0.height);
                    if ((p0.y + p0.height) != p1.y) {
                        g.drawRect(alloc.x, p0.y + p0.height, alloc.width-1,
                                   p1.y - (p0.y + p0.height)-1);
                    }
                    g.drawRect(alloc.x, p1.y, (p1.x - alloc.x)-1, p1.height-1);
                }
            } catch (BadLocationException e) {
                // can't render
            }
        }
    }

}
