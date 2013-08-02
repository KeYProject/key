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

package de.uka.ilkd.key.gui.nodeviews;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.configuration.ConfigChangeAdapter;
import de.uka.ilkd.key.gui.configuration.ConfigChangeListener;
import static de.uka.ilkd.key.gui.nodeviews.CurrentGoalView.ADDITIONAL_HIGHLIGHT_COLOR;
import static de.uka.ilkd.key.gui.nodeviews.CurrentGoalView.DEFAULT_HIGHLIGHT_COLOR;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.pp.SequentPrintFilter;
import de.uka.ilkd.key.util.Debug;
import java.awt.Color;
import java.awt.Font;
import java.awt.Point;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.event.MouseMotionListener;
import java.util.HashMap;
import java.util.LinkedHashMap;

import javax.swing.JTextArea;
import javax.swing.UIManager;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter;
import javax.swing.text.Highlighter;

/*
 * Parent class of CurrentGoalView and InnerNodeView.
 */
public abstract class SequentView extends JTextArea
        implements KeyListener, MouseMotionListener, MouseListener {

    private final MainWindow mainWindow;
    
    /* 
     * The current line width. Static declaration for this prevents constructors from
     * using lineWidth 0.
     */
    private static int lineWidth;
    
    public static void setLineWidth(int i) {
        if (i != 0) {
            lineWidth = i;
        }
    }
    
    public static int getLineWidth() {
        return lineWidth;
    }
    
    private ConfigChangeListener configChangeListener;
    SequentPrintFilter filter;
    LogicPrinter printer;
    public boolean refreshHighlightning = true;
    private boolean showTermInfo = false;
    
    // the default tag of the highlight
    private final Object defaultHighlight;

    // the current tag of the highlight
    private Object currentHighlight;

    // an additional highlight to mark the first active java statement
    private final Object additionalJavaHighlight;
    
    // Highlighting color during drag and drop action.
    public final Object dndHighlight;
    
    /*
     * Store highlights in a HashMap in order to prevent duplicate highlights.
     */
    private HashMap<Color, DefaultHighlighter.DefaultHighlightPainter> color2Highlight =
            new LinkedHashMap<Color, DefaultHighlighter.DefaultHighlightPainter>();

    SequentView(MainWindow mainWindow) {
        this.mainWindow = mainWindow;

        configChangeListener = new ConfigChangeAdapter(this);
        Config.DEFAULT.addConfigChangeListener(configChangeListener);
        setEditable(false);
        setBackground(new Color(249, 249, 249));
        setFont();
        addKeyListener(this);
        addMouseMotionListener(this);
        addMouseListener(this);
        
	// sets the painter for the highlightning
	setHighlighter(new DefaultHighlighter());
        additionalJavaHighlight = getColorHighlight(ADDITIONAL_HIGHLIGHT_COLOR);
	defaultHighlight = getColorHighlight(DEFAULT_HIGHLIGHT_COLOR);
        dndHighlight = getColorHighlight(CurrentGoalView.DND_HIGHLIGHT_COLOR);
	currentHighlight = defaultHighlight;

        // add a SeqViewChangeListener to this component
        SeqViewChangeListener changeListener = new SeqViewChangeListener(this);
        addComponentListener(changeListener);
        addPropertyChangeListener("font", changeListener);
        addHierarchyBoundsListener(changeListener);
    }
    
    public void setFont() {
        Font myFont = UIManager.getFont(Config.KEY_FONT_SEQUENT_VIEW);
        if (myFont != null) {
            setFont(myFont);
        } else {
            Debug.out("KEY_FONT_SEQUENT_VIEW not available. Use standard font.");
        }
    }
    
    public void unregisterListener() {
        if (configChangeListener != null) {
            Config.DEFAULT.removeConfigChangeListener(configChangeListener);
        }
    }

    @Override
    public void addNotify() {
        super.addNotify();
        Config.DEFAULT.addConfigChangeListener(configChangeListener);
        updateUI();
    }

    @Override
    public void removeNotify() {
        super.removeNotify();
        unregisterListener();
    }
    
    @Override
    protected void finalize() {
        try {
            unregisterListener();
        } catch (Throwable e) {
            mainWindow.notify(new GeneralFailureEvent(e.getMessage()));
        } finally {
            try {
                super.finalize();
            } catch (Throwable e) {
                mainWindow.notify(new GeneralFailureEvent(e.getMessage()));
            }
        }
    }

    public void removeHighlight(Object highlight) {
        getHighlighter().removeHighlight(highlight);
    }

    /**
     * highlights the elements in the given range using the specified
     * highlighter
     *
     * @param range the Range to be highlighted
     * @param highlighter the Object painting the highlight
     */
    void paintHighlight(Range range, Object highlighter) {
        try {
            if (range != null) {
                getHighlighter()
                        .changeHighlight(highlighter,
                        range.start(), range.end());
            } else {
                getHighlighter()
                        .changeHighlight(highlighter, 0, 0);
            }
        } catch (BadLocationException badLocation) {
            System.err.println("SequentView tried to highlight an area"
                    + "that is not existing.");
            badLocation.printStackTrace();
        }
    }

    /**
     * registers a highlighter that marks the regions specified by the returned
     * tag with the given color
     *
     * @param color the Color used to highlight regions of the sequent
     * @return the highlight for the specified color
     */
    public Object getColorHighlight(Color color) {
        Object highlight = null;
        if (!color2Highlight.containsKey(color)) {
            color2Highlight.put(color,
                    new DefaultHighlighter.DefaultHighlightPainter(color));
        }
        Highlighter.HighlightPainter hp = color2Highlight.get(color);
        try {
            highlight =
                    getHighlighter().addHighlight(0, 0, hp);
        } catch (BadLocationException e) {
            Debug.out("Highlight range out of scope.");
            e.printStackTrace();
        }
        return highlight;
    }

    public abstract String getTitle();

    /**
     * Get a PosInSequent object for a given coordinate of the displayed
     * sequent.
     */
    protected synchronized PosInSequent getPosInSequent(Point p) {
        String seqText = getText();
        if (seqText.length() > 0 && p != null) {
            int characterIndex = correctedViewToModel(p);
            return printer.getInitialPositionTable().
                    getPosInSequent(characterIndex, filter);
        } else {
            return null;
        }
    }

    public String getHighlightedText(PosInSequent pos) {
        String s = "";
        try {
            s = getText(pos.getBounds().start(),
                    pos.getBounds().length());
        } catch (Exception e) {
            e.printStackTrace();
        }
        return s;
    }

    private void showTermInfo(Point p) {

        if (showTermInfo) {

            PosInSequent mousePos = getPosInSequent(p);
            String info = null;

            if ((mousePos != null)
                    && !("".equals(getHighlightedText(mousePos)))) {

                Term t;
                final PosInOccurrence posInOcc = mousePos.getPosInOccurrence();
                if (posInOcc != null) {
                    t = posInOcc.subTerm();
                    String tOpClassString = t.op().getClass().toString();
                    String operator = tOpClassString.substring(
                            tOpClassString.lastIndexOf('.') + 1);
                    // What is the purpose of displaying the java hashcode here?
                    info = operator + ", Sort: " + t.sort() + ", Hash:" + t.hashCode();
                }
            }

            if (info == null) {
                mainWindow.setStandardStatusLine();
            } else {
                mainWindow.setStatusLine(info);
            }

        }

    }

    /**
     * Return the character index for a certain coordinate. The usual
     * viewToModel is focussed on inter-character spaces, not characters, so it
     * returns the correct index in the left half of the glyph but one too many
     * in the right half. Therefore, we get width of character before the one
     * given by viewToModel, substract it from the given x value, and get the
     * character at the new position. That is the correct one.
     */
    public int correctedViewToModel(Point p) {
        String seqText = getText();
        int cursorPosition = viewToModel(p);
        cursorPosition -= (cursorPosition > 0 ? 1 : 0);
        cursorPosition = (cursorPosition >= seqText.length()
                ? seqText.length() - 1
                : cursorPosition);
        cursorPosition = (cursorPosition >= 0 ? cursorPosition : 0);
        int previousCharacterWidth =
                getFontMetrics(getFont()).charWidth(seqText.charAt(cursorPosition));
        int characterIndex = viewToModel(new Point((int) p.getX() - (previousCharacterWidth / 2),
                (int) p.getY()));
        return characterIndex;
    }
    
    /**
     * removes highlight by setting it to position (0,0)
     */
    public void disableHighlight(Object highlight) {
        try {
            getHighlighter().changeHighlight(highlight,0,0);
        } catch (BadLocationException e) {
            Debug.out("Invalid range for highlight");
            e.printStackTrace();
        }
    }
    
    /**
     * removes the term and first statement highlighter by setting them to 
     * position (0,0)     
     */
    public void disableHighlights() {
        disableHighlight(currentHighlight);
        disableHighlight(additionalJavaHighlight);        
    }
    
    /** 
     * sets the correct highlighter for the given color  
     * @param tag the Object used as tag for highlighting     
     */
    public void setCurrentHighlight(Object tag) {                
        currentHighlight = tag;
    }
    
    /**
     * returns the current tag used for highligthing
     * @return the current tag used for highlighting
     */
    public Object getCurrentHighlight() {        
        return currentHighlight;
    }
    
    /** the startposition and endposition+1 of the string to be
     * highlighted
     * @param p the mouse pointer coordinates
     */
    public void paintHighlights(Point p) {
	// Change highlight for additional Java statement ...
	paintHighlight(getFirstStatementRange(p), additionalJavaHighlight);
	// Change Highlighter for currently selected sequent part 
	paintHighlight(getHighlightRange(p), currentHighlight);
    }
    
    /** Get the character range to be highlighted for the given
     * coordinate in the displayed sequent. */
    synchronized Range getHighlightRange(Point p) {
	String seqText = getText();
	if (seqText.length() > 0) {
	    int characterIndex = correctedViewToModel(p);	    
	    return printer.getInitialPositionTable().
		rangeForIndex(characterIndex);
	} else {
	    return null;
	}
    }

    /** Get the character range to be highlighted for the first
     * statement in a java block at the given
     * coordinate in the displayed sequent.  Returns null
     * if there is no java block there.*/
    protected synchronized Range getFirstStatementRange(Point p) {
	String seqText = getText();
	if (seqText.length() > 0) {
	    int characterIndex = correctedViewToModel(p);
	    return printer.getInitialPositionTable().
		firstStatementRangeForIndex(characterIndex);
	} else {
	    return null;
	}
    }
    
    public void highlight(Point p) {
        setCurrentHighlight(defaultHighlight);
        paintHighlights(p);
    }

    public void mouseClicked(MouseEvent e) {
        // Necessary for MouseListener Interface
    }

    public void mousePressed(MouseEvent e) {
        // Necessary for MouseListener Interface
    }

    public void mouseReleased(MouseEvent e) {
        // Necessary for MouseListener Interface
    }

    public void mouseEntered(MouseEvent e) {
        // Requesting focus here is necessary for the
        // ALT KeyListener, which works in combination with
        // mouseMoved Events.
        requestFocusInWindow();
    }

    public void mouseDragged(MouseEvent me) {
        // Necessary for MouseMotionListener Interface
    }

    public void mouseMoved(MouseEvent me) {
        showTermInfo(me.getPoint());
        if (refreshHighlightning) {
            highlight(me.getPoint());
        }
    }
    
    public void mouseExited(MouseEvent e) {
        if (refreshHighlightning) {
            disableHighlights();
        }
    }

    public void keyTyped(KeyEvent e) {
        // Necessary for KeyListener Interface
    }

    /* (non-Javadoc)
     * @see java.awt.event.KeyListener#keyPressed(java.awt.event.KeyEvent)
     */
    public void keyPressed(KeyEvent e) {
        if ((e.getModifiersEx() & InputEvent.ALT_DOWN_MASK) != 0) {
            showTermInfo = true;
            showTermInfo(getMousePosition());
        }
    }

    /* (non-Javadoc)
     * @see java.awt.event.KeyListener#keyReleased(java.awt.event.KeyEvent)
     */
    public void keyReleased(KeyEvent e) {
        if ((e.getModifiersEx() & InputEvent.ALT_DOWN_MASK) == 0 && showTermInfo) {
            showTermInfo = false;
            mainWindow.setStandardStatusLine();
        }
    }
    
    @Override
    public void updateUI() {
        super.updateUI();
        setFont();
    }
    
    /**
     * computes the line width
     */
    public int computeLineWidth() {
        // assumes we have a uniform font width
        int maxChars = (int) 
            (getVisibleRect().getWidth()/getFontMetrics(getFont()).charWidth('W'));
        
        if (maxChars > 1) maxChars-=1;
        return maxChars;
    }
    
    public abstract void printSequent();

}
