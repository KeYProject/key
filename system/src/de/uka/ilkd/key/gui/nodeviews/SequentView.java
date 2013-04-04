package de.uka.ilkd.key.gui.nodeviews;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.Config;
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
import javax.swing.JTextArea;
import javax.swing.UIManager;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter;
import javax.swing.text.Highlighter;

/*
 * Parent class of LeafNodeView and InnerNodeView.
 */
public abstract class SequentView extends JTextArea
        implements KeyListener, MouseMotionListener, MouseListener {

    SequentPrintFilter filter;
    LogicPrinter printer;
    public static final Color BACKGROUND_COLOR = new Color(249, 249, 249);
    
    // all known highlights
    private HashMap<Color, DefaultHighlighter.DefaultHighlightPainter> color2Highlight =
            new HashMap<Color, DefaultHighlighter.DefaultHighlightPainter>();
    
    /* 
     * The MainFrame border displays a button in the top-left corner.
     * Each SequentView has it and can be used for custom actions.
     */
    public TitleButton titleButton;

    SequentView() {

        titleButton = new TitleButton(this);
        setEditable(false);
        setBackground(BACKGROUND_COLOR);
        Font myFont = UIManager.getFont(Config.KEY_FONT_SEQUENT_VIEW);
        if (myFont != null) {
            setFont(myFont);
        } else {
            Debug.out("KEY_FONT_SEQUENT_VIEW not available. Use standard font.");
        }
        addKeyListener(this);
        addMouseMotionListener(this);
        addMouseListener(this);

    }

    /**
     * d a highlighter that marks the regions specified by the returned tag with
     * the given color
     *
     * @param highlight the Object used as tag for the highlight
     */
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
            // Change highlight for additional Java statement ...
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
            System.err.println("Exception:" + badLocation);
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
        if (seqText.length() > 0) {
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

    private boolean showTermInfo = false;
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
                MainWindow.getInstance().setStandardStatusLine();
            } else {
                MainWindow.getInstance().setStatusLine(info);
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

    public void mouseExited(MouseEvent e) {
        // Necessary for MouseListener Interface
    }

    public void mouseDragged(MouseEvent me) {
        // Necessary for MouseMotionListener Interface
    }

    public void mouseMoved(MouseEvent me) {
        showTermInfo(me.getPoint());
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
            MainWindow.getInstance().setStandardStatusLine();
        }
    }

}
