package de.uka.ilkd.key.gui.nodeviews;

import static de.uka.ilkd.key.gui.nodeviews.LeafNodeView.UPDATE_HIGHLIGHT_COLOR;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.util.Debug;
import java.awt.Color;
import java.util.HashMap;
import java.util.Vector;
import javax.swing.JTextArea;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter;
import javax.swing.text.Highlighter;

/*
 * Parent class of LeafNodeView and InnerNodeView.
 */
public abstract class SequentView extends JTextArea {

    // all known highlights
    private HashMap<Color, DefaultHighlighter.DefaultHighlightPainter> color2Highlight =
            new HashMap<Color, DefaultHighlighter.DefaultHighlightPainter>();
    
    SequentView(){
        setEditable(false);
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
}
