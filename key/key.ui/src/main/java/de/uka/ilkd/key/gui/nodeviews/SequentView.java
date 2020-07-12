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

package de.uka.ilkd.key.gui.nodeviews;

import static de.uka.ilkd.key.gui.nodeviews.CurrentGoalView.ADDITIONAL_HIGHLIGHT_COLOR;
import static de.uka.ilkd.key.gui.nodeviews.CurrentGoalView.DEFAULT_HIGHLIGHT_COLOR;

import java.awt.Color;
import java.awt.Font;
import java.awt.Graphics;
import java.awt.Point;
import java.awt.Shape;
import java.awt.event.MouseEvent;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.Objects;
import java.util.StringJoiner;

import javax.swing.JEditorPane;
import javax.swing.UIManager;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter;
import javax.swing.text.DefaultHighlighter.DefaultHighlightPainter;
import javax.swing.text.Highlighter;
import javax.swing.text.Highlighter.HighlightPainter;
import javax.swing.text.JTextComponent;
import javax.swing.text.html.HTMLDocument;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.configuration.ConfigChangeAdapter;
import de.uka.ilkd.key.gui.configuration.ConfigChangeListener;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.logic.FormulaChangeInfo;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.IdentitySequentPrintFilter;
import de.uka.ilkd.key.pp.InitialPositionTable;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.pp.SequentPrintFilter;
import de.uka.ilkd.key.pp.SequentPrintFilterEntry;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.pp.VisibleTermLabels;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;
import de.uka.ilkd.key.util.Debug;

/*
 * Parent class of CurrentGoalView and InnerNodeView.
 */
public abstract class SequentView extends JEditorPane {
    private static final long serialVersionUID = 6867808795064180589L;

    public static final Color PERMANENT_HIGHLIGHT_COLOR = new Color(110, 85, 181, 76);

    public static final Color DND_HIGHLIGHT_COLOR = new Color(0, 150, 130, 104);

    protected static final Color UPDATE_HIGHLIGHT_COLOR = new Color(0, 150, 130, 38);

    protected static final Color INACTIVE_BACKGROUND_COLOR
            = new Color(UIManager.getColor("Panel.background").getRGB());

    //
    private static final ColorSettings.ColorProperty HEATMAP_COLOR =
            ColorSettings.define("[Heatmap]basecolor",
                    "Base color of the heatmap. Other colors are derived from this one.",
                    new Color(252, 202, 80));

    //maximum opacity of heatmap color
    private static final float HEATMAP_DEFAULT_START_OPACITY = .7f;
    public static final String PROP_LAST_MOUSE_POSITION = "lastMousePosition";

    private final MainWindow mainWindow;

    public MainWindow getMainWindow() {
        return mainWindow;
    }

    /**
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

    public VisibleTermLabels getVisibleTermLabels() {
        return mainWindow.getVisibleTermLabels();
    }

    private final ConfigChangeListener configChangeListener;
    protected SequentPrintFilter filter;
    private SequentViewLogicPrinter printer;
    private HTMLSyntaxHighlighter syntaxHighlighter;
    public boolean refreshHighlightning = true;

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
    private final HashMap<Color, HighlightPainter> color2Highlight
            = new LinkedHashMap<>();

    /** the last observed mouse position for which a highlight was created */
    private Point lastMousePosition;

    private SequentViewInputListener sequentViewInputListener;

    private Object userSelectionHighlight = null;
    private Range userSelectionHighlightRange = null;
    private PosInSequent userSelectionHighlightPis = null;

    protected SequentView(MainWindow mainWindow) {
        this.mainWindow = mainWindow;

        setContentType("text/html");
        syntaxHighlighter = new HTMLSyntaxHighlighter((HTMLDocument)getDocument());

        configChangeListener = new ConfigChangeAdapter(this);
        Config.DEFAULT.addConfigChangeListener(configChangeListener);
        setEditable(false);
        setFont();

        sequentViewInputListener = new SequentViewInputListener(this);
        addMouseMotionListener(sequentViewInputListener);
        addMouseListener(sequentViewInputListener);

        // sets the painter for the highlightning
        setHighlighter(new DefaultHighlighter());
        additionalJavaHighlight = getColorHighlight(ADDITIONAL_HIGHLIGHT_COLOR.get());
        defaultHighlight = getColorHighlight(DEFAULT_HIGHLIGHT_COLOR.get());
        dndHighlight = getColorHighlight(CurrentGoalView.DND_HIGHLIGHT_COLOR.get());
        currentHighlight = defaultHighlight;

        // add a SeqViewChangeListener to this component
        SequentViewChangeListener changeListener = new SequentViewChangeListener(this);
        addComponentListener(changeListener);
        addPropertyChangeListener("font", changeListener);
        addHierarchyBoundsListener(changeListener);

        filter = new IdentitySequentPrintFilter();

        // Register tooltip
        setToolTipText("");

        KeYGuiExtensionFacade.installKeyboardShortcuts(getMainWindow().getMediator(),
                this, KeYGuiExtension.KeyboardShortcuts.SEQUENT_VIEW);
    }

    public final void setFont() {
        Font myFont = UIManager.getFont(Config.KEY_FONT_SEQUENT_VIEW);
        if (myFont != null) {
            putClientProperty(JEditorPane.HONOR_DISPLAY_PROPERTIES, Boolean.TRUE);
            setFont(myFont);
        } else {
            Debug.out("KEY_FONT_SEQUENT_VIEW not available. Use standard font.");
        }
    }

    public void unregisterListener() {
       Config.DEFAULT.removeConfigChangeListener(configChangeListener);
    }

    @Override
    public String getToolTipText(MouseEvent event) {
        if (!ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .isShowSequentViewTooltips()) {
            return null;
        }

        PosInSequent pis = getPosInSequent(event.getPoint());

        String text = "";

        if (pis != null && !pis.isSequent()) {
            Term term = pis.getPosInOccurrence().subTerm();
            text += "<b>Operator:</b> " + term.op().getClass().getSimpleName()
                    + " (" + term.op() + ")";
            text += "<br><b>Sort</b>: " + term.sort();
        }

        StringJoiner extensionStr = new StringJoiner("<hr>", "<hr>", "");
        extensionStr.setEmptyValue("");
        KeYGuiExtensionFacade.getTooltipStrings(getMainWindow(), pis).stream()
            .filter(s -> !s.isEmpty())
            .forEach(extensionStr::add);
        text += extensionStr;

        if (text.isEmpty()) {
            return null;
        } else {
            return "<html>" + text + "</html>";
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
    public void paintHighlight(Range range, Object highlighter) {
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
            System.err.println("SequentView tried to highlight an area "
                    + "that does not exist: "+range);
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
    public final Object getColorHighlight(Color color) {
        Object highlight = null;
        if (!color2Highlight.containsKey(color)) {
            // show highlights above each other
            // https://stackoverflow.com/questions/9083206/how-to-use-layeredhighlighter-one-highlight-on-top-of-another
            final HighlightPainter painter = new Highlighter.HighlightPainter() {
                final DefaultHighlightPainter helper = new DefaultHighlighter.DefaultHighlightPainter(color);
                @Override
                public void paint(Graphics g, int p0, int p1, Shape bounds, JTextComponent c) {
                    helper.paint(g, p0, p1, bounds, c);
                }
            };
            color2Highlight.put(color, painter);
        }
        Highlighter.HighlightPainter hp = color2Highlight.get(color);
        try {
            highlight
                    = getHighlighter().addHighlight(0, 0, hp);
        } catch (BadLocationException e) {
            Debug.out("Highlight range out of scope.");
            e.printStackTrace();
        }
        return highlight;
    }

    public abstract String getTitle();

    /* (non-Javadoc)
     * @see javax.swing.JEditorPane#getText()
     */
    /**
     * Returns the plain text of this sequent view.
     */
    @Override
    public String getText() {
        try {
            return getDocument().getText(0, getDocument().getLength());
        }
        catch (BadLocationException e) {
            return super.getText(); // shouldn't happen
        }
    }

    /**
     * Get the PosInSequent object for the last observed
     * and highlighted mouse position.
     */
    public PosInSequent getLastPosInSequent() {
        return getPosInSequent(lastMousePosition);
    }

    /**
     * Get a PosInSequent object for a given coordinate of the displayed
     * sequent.
     */
    protected synchronized PosInSequent getPosInSequent(Point p) {
        String seqText = getText();
        if (seqText.length() > 0 && p != null) {
            int characterIndex = correctedViewToModel(p);
            return printer.getInitialPositionTable().
                    getPosInSequent(characterIndex, getFilter());
        } else {
            return null;
        }
    }

    /**
     * Return used LogicPrinter.
     *
     * @return The LogicPrinter that is used.
     */
    public SequentViewLogicPrinter getLogicPrinter() {
        return printer;
    }

    /**
     * Set the LogicPrinter to be used.
     *
     * @param p The LogicPrinter to be used
     */
    protected void setLogicPrinter(SequentViewLogicPrinter p) {
        printer = p;
    }

    /**
     * @return The HTML syntax highlighter used for this sequent view.
     */
    protected HTMLSyntaxHighlighter getSyntaxHighlighter() {
        return syntaxHighlighter;
    }

    public String getHighlightedText(PosInSequent pos) {
        if (pos == null) {
            return "";
        }
        String s = "";
        try {
            // NOTE (DS): The below addition of 1 to the beginning is a
            // quick-and-dirty fix for the problem that the copied text
            // was one position shifted to the left (occurred after the
            // change to HTML documents in the JEditorPane (previous JTextArea)). If
            // something concerning highlighting does not work in the future, here
            // could be a starting place to find the mistake.
            s = getText(pos.getBounds().start() + 1,
                    pos.getBounds().length());
        } catch (BadLocationException e) {
            e.printStackTrace();
        }
        return s;
    }

    public String getHighlightedText() {
        return getHighlightedText(getPosInSequent(getMousePosition()));
    }

    /**
     * Return the character index for a certain coordinate. The usual
     * viewToModel is focused on inter-character spaces, not characters, so it
     * returns the correct index in the left half of the glyph but one too many
     * in the right half. Therefore, we get width of character before the one
     * given by viewToModel, subtract it from the given x value, and get the
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
        int previousCharacterWidth
                = getFontMetrics(getFont()).charWidth(seqText.charAt(cursorPosition));
        int characterIndex = viewToModel(new Point((int) p.getX() - (previousCharacterWidth / 2),
                (int) p.getY()));

        // NOTE (DS): The below subtraction of 1 to the beginning is a
        // quick-and-dirty fix for the problem that the mouse pointer
        // has to point to the element one position left of the actual
        // element that should be highlighted (occurred after the
        // change to HTML documents in the JEditorPane (previous JTextArea)). If
        // something concerning highlighting does not work in the future, here
        // could be a starting place to find the mistake.

        return characterIndex - 1;
    }

    /**
     * removes highlight by setting it to position (0,0)
     */
    public void disableHighlight(Object highlight) {
        try {
            getHighlighter().changeHighlight(highlight, 0, 0);
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
     *
     * @param tag the Object used as tag for highlighting
     */
    public void setCurrentHighlight(Object tag) {
        currentHighlight = tag;
    }

    /**
     * returns the current tag used for highligthing
     *
     * @return the current tag used for highlighting
     */
    public Object getCurrentHighlight() {
        return currentHighlight;
    }

    /**
     * the startposition and endposition+1 of the string to be highlighted
     *
     * @param p the mouse pointer coordinates
     */
    public void paintHighlights(Point p) {
        // Change highlight for additional Java statement ...
        paintHighlight(getFirstStatementRange(p), additionalJavaHighlight);
        // Change Highlighter for currently selected sequent part
        paintHighlight(getHighlightRange(p), currentHighlight);
    }

    /**
     * Get the character range to be highlighted for the given coordinate in the
     * displayed sequent.
     */
    synchronized Range getHighlightRange(Point p) {
        String seqText = getText();
        if (seqText.length() > 0) {
            int characterIndex = correctedViewToModel(p);

            // NOTE (DS): The below addition of 1 to the beginning is a quick-and-dirty
            // fix for a shift of highlighted areas to the left that occurred after the
            // change to HTML documents in the JEditorPane (previous JTextArea). If
            // something concerning highlighting does not work in the future, here could
            // be a starting place to find the mistake.
            Range result = printer.getInitialPositionTable().rangeForIndex(characterIndex);
            result = new Range(result.start() + 1, result.end() + 1);

            return result;
        } else {
            return null;
        }
    }

    /**
     * Get the character range to be highlighted for the first statement in a
     * java block at the given coordinate in the displayed sequent. Returns null
     * if there is no java block there.
     */
    protected synchronized Range getFirstStatementRange(Point p) {
        if (getDocument().getLength() > 0) {
            int characterIndex = correctedViewToModel(p);
            Range result = printer.getInitialPositionTable().
                    firstStatementRangeForIndex(characterIndex);
            if (result == null) {
                return null;
            }
            else {
                return new Range(result.start() + 1, result.end() + 1);
            }
        } else {
            return null;
        }
    }

    /**
     * Updates the head map highlights.
     */
    protected void updateHeatMapHighlights() {
        ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        int max_age = vs.getMaxAgeForHeatmap();
        if (vs.isShowHeatmap()) {
            if (vs.isHeatmapSF()) {
                if (vs.isHeatmapNewest()) {
                    updateHeatmapSFHighlights(max_age, true);
                } else {
                    updateHeatmapSFHighlights(max_age, false);
                }
            } else {
                if (vs.isHeatmapNewest()) {
                    updateHeatmapTermHighlights(max_age, true);
                } else {
                    updateHeatmapTermHighlights(max_age, false);
                }
            }
        }
    }

    Range getUserSelectionHighlightRange() {
        return userSelectionHighlightRange;
    }

    void recalculateUserSelectionRange() {
        if (userSelectionHighlight == null) {
            return;
        }

        InitialPositionTable posTable = printer.getInitialPositionTable();
        PosInSequent pis = userSelectionHighlightPis;
        Range range = posTable.rangeForPath(
                posTable.pathForPosition(pis.getPosInOccurrence(), filter));

        removeUserSelectionHighlight();

        try {
            userSelectionHighlightPis = pis;
            userSelectionHighlightRange = new Range(range.start() + 1, range.end() + 1);
            userSelectionHighlight = getHighlighter().addHighlight(
                    userSelectionHighlightRange.start(), userSelectionHighlightRange.end(),
                    new DefaultHighlightPainter(PERMANENT_HIGHLIGHT_COLOR));

            sequentViewInputListener.highlightOriginInSourceView(pis);
        } catch (BadLocationException e) {
            Debug.out("Error while setting permanent highlight", e);
        }
    }

    protected void setUserSelectionHighlight(Point point) {
        removeUserSelectionHighlight();

        try {
            userSelectionHighlightPis = getPosInSequent(point);
            userSelectionHighlightRange = getHighlightRange(point);
            userSelectionHighlight = getHighlighter().addHighlight(
                    userSelectionHighlightRange.start(), userSelectionHighlightRange.end(),
                    new DefaultHighlightPainter(PERMANENT_HIGHLIGHT_COLOR));

            sequentViewInputListener.highlightOriginInSourceView(userSelectionHighlightPis);
        } catch (BadLocationException e) {
            Debug.out("Error while setting permanent highlight", e);
        }
    }

    /**
     * Removes the user selection.
     *
     * @see #setUserSelectionHighlight(PosInSequent)
     * @see #setUserSelectionHighlight(Point)
     * @see #isInUserSelectionHighlight(Point)
     */
    protected void removeUserSelectionHighlight() {
        if (userSelectionHighlight != null) {
            getHighlighter().removeHighlight(userSelectionHighlight);
        }

        userSelectionHighlight = null;
        userSelectionHighlightPis = null;
        userSelectionHighlightRange = null;

        sequentViewInputListener.highlightOriginInSourceView(null);
    }

    /**
     *
     * @param point a point.
     * @return {@code true} if and only if the argument points to the user selection.
     *
     * @see #setUserSelectionHighlight(PosInSequent)
     * @see #setUserSelectionHighlight(Point)
     * @see #removeUserSelectionHighlight()
     */
    protected boolean isInUserSelectionHighlight(Point point) {
        return point == null && userSelectionHighlightRange == null
                || point != null && userSelectionHighlightRange != null
                        && Objects.equals(
                                userSelectionHighlightRange,
                                getHighlightRange(point));
    }

    /**
     * Highlights the term at the specified position as the user's selection.
     *
     * @param pis the term to select.
     *
     * @see #setUserSelectionHighlight(Point)
     * @see #removeUserSelectionHighlight()
     * @see #isInUserSelectionHighlight(Point)
     */
    protected void setUserSelectionHighlight(PosInSequent pis) {
        removeUserSelectionHighlight();

        try {
            userSelectionHighlightRange = new Range(pis.getBounds().start(), pis.getBounds().end());
            userSelectionHighlight = getHighlighter().addHighlight(
                    userSelectionHighlightRange.start(), userSelectionHighlightRange.end(),
                    new DefaultHighlightPainter(PERMANENT_HIGHLIGHT_COLOR));

            sequentViewInputListener.highlightOriginInSourceView(pis);
        } catch (BadLocationException e) {
            Debug.out("Error while setting permanent highlight", e);
        }
    }


    public void highlight(Point p) {
        setCurrentHighlight(defaultHighlight);
        paintHighlights(p);
        setLastMousePosition(p);
    }

    private void setLastMousePosition(Point p) {
        Point old = this.lastMousePosition;
        lastMousePosition=p;
        firePropertyChange(PROP_LAST_MOUSE_POSITION, old, p);
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
        int maxChars = (int) (getVisibleRect().getWidth() / getFontMetrics(getFont()).charWidth('W'));

        if (maxChars > 1) {
            maxChars -= 1;
        }
        return maxChars;
    }

    /**
     * Highlights sequent formulas according to their age (if newest is false),
     * or the newest sequent formulas.
     * @param max_age maximum age up to which sf's are highlighted, or number of recent sf's to highlight.
     * @param newest Are newest sf's highlighted (true) or all up to max_age (false)?
     */
    protected void updateHeatmapSFHighlights(int max_age, boolean newest) {
        if (getLogicPrinter() == null) {
            return;
        }

        InitialPositionTable ipt = getLogicPrinter().getInitialPositionTable();

        int i = 0;

        // 5 "youngest" sequent formulas are highlighted.
        ImmutableList<SequentPrintFilterEntry> entryList = filter.getFilteredAntec().append(filter.getFilteredSucc());
        if (newest) {
            SequentPrintFilterEntry[] sortedArray = new SequentPrintFilterEntry[entryList.size()];
            entryList.toArray(sortedArray);
            Arrays.sort(sortedArray, new Comparator<SequentPrintFilterEntry>() {
                @Override
                public int compare(SequentPrintFilterEntry o1, SequentPrintFilterEntry o2) {
                    int o1age = computeSeqFormulaAge(getMainWindow().getMediator().getSelectedNode(),
                            o1.getFilteredFormula(), 1000);
                    int o2age = computeSeqFormulaAge(getMainWindow().getMediator().getSelectedNode(),
                            o2.getFilteredFormula(), 1000);
                    return o1age - o2age;
                }
            });
            for (SequentPrintFilterEntry entry : entryList) {
                for (int j = 0; j < max_age && j < sortedArray.length; ++j) {
                    if (sortedArray[j].equals(entry)) {
                        Color color = computeColorForAge(max_age, j);
                        ImmutableSLList<Integer> list = (ImmutableSLList<Integer>) ImmutableSLList.<Integer>nil()
                                .prepend(0).append(i);
                        Range r = ipt.rangeForPath(list);
                        Range newR = new Range(r.start() + 1, r.end() + 1); // Off-by-one: siehe updateUpdateHighlights bzw in InnerNodeView. rangeForPath ist schuld
                        Object tag = getColorHighlight(color);
                        paintHighlight(newR, tag);
                    }
                }
                ++i;
            }
        } else {    // all formulas below MAX_AGE_FOR_HEATMAP are highlighted.
            for(SequentPrintFilterEntry entry : entryList) {
                SequentFormula form = entry.getFilteredFormula();
                int age = computeSeqFormulaAge(getMainWindow().getMediator().getSelectedNode(), form, max_age + 2);
                if(age < max_age) {
                    Color color = computeColorForAge(max_age, age);
                    ImmutableSLList<Integer> list = (ImmutableSLList<Integer>) ImmutableSLList.<Integer>nil().prepend(0).append(i);
                    Range r = ipt.rangeForPath(list);
                    Range newR = new Range(r.start()+1, r.end()+1); // Off-by-one: siehe updateUpdateHighlights bzw in InnerNodeView. rangeForPath ist schuld
                    Object tag = getColorHighlight(color);
                    paintHighlight(newR, tag);
                }
                ++i;
            }
        }
    }

    /**
     * Highlights terms according to their age (if newest is false),
     * or the newest terms.
     * @param max_age maximum age up to which terms are highlighted, or number of recent terms to highlight.
     * @param newest Are newest terms highlighted (true) or all up to max_age (false)?
     */
    protected void updateHeatmapTermHighlights(int max_age, boolean newest) {
        LinkedList<Node> nodeList = new LinkedList<>();
        Node node = getMainWindow().getMediator().getSelectedNode();
        nodeList.add(node);
        // some sort of limit might make sense here for big sequents, but since
        // for the newest term heatmap duplicates will be removed,
        // this list has to be longer than max_age_for_heatmap.
        while (node.parent() != null) {
            node = node.parent();
            nodeList.addFirst(node);
        }
        ArrayList<PIO_age> pio_age_list = new ArrayList<>();
        Iterator<Node> it = nodeList.iterator();
        int age = nodeList.size() - 1;

        // preparation of the list of terms
        while (it.hasNext()) {
            node = it.next();
            if (node.getNodeInfo().getSequentChangeInfo() != null) {
                ImmutableList<SequentFormula> added_ante = node.getNodeInfo().getSequentChangeInfo().addedFormulas(true);
                ImmutableList<SequentFormula> added_succ = node.getNodeInfo().getSequentChangeInfo().addedFormulas(false);
                for (SequentFormula sf : added_ante) {
                    pio_age_list.add(new PIO_age(new PosInOccurrence(sf, PosInTerm.getTopLevel(), true), age));
                }
                for (SequentFormula sf : added_succ) {
                    pio_age_list.add(new PIO_age(new PosInOccurrence(sf, PosInTerm.getTopLevel(), false), age));
                }
                ImmutableList<FormulaChangeInfo> modified = node.getNodeInfo().getSequentChangeInfo().modifiedFormulas();
                for (FormulaChangeInfo fci : modified) {
                    PosInOccurrence positionOfMod = fci.getPositionOfModification();
                    pio_age_list.add(new PIO_age(positionOfMod, age));
                    for (PIO_age pair : pio_age_list) {
                        if (pair.get_pio().sequentFormula().equals(fci.getOriginalFormula())) {
                            if(positionOfMod.posInTerm().isPrefixOf(pair.get_pio().posInTerm())) {
                                pair.active = false;
                            } else {
                                pair.set_pio(new PosInOccurrence(fci.getNewFormula(), pair.get_pio().posInTerm(), pair.get_pio().isInAntec()));
                            }
                        }
                    }
                }
                for (SequentFormula sf : node.getNodeInfo().getSequentChangeInfo().removedFormulas(true)) {
                    for (PIO_age pair : pio_age_list) {
                        if (pair.get_pio().sequentFormula().equals(sf) && pair.get_pio().isInAntec()) {
                            pair.active = false;
                        }
                    }
                }
                for (SequentFormula sf : node.getNodeInfo().getSequentChangeInfo().removedFormulas(false)) {
                    for (PIO_age pair : pio_age_list) {
                        if (pair.get_pio().sequentFormula().equals(sf) && !pair.get_pio().isInAntec()) {
                            pair.active = false;
                        }
                    }
                }

            }
            --age;
        }
        InitialPositionTable ipt = getLogicPrinter().getInitialPositionTable();

        pio_age_list.sort(new Comparator<PIO_age>() {
                @Override
                public int compare(PIO_age o1, PIO_age o2) {
                    return o1.age >= o2.age ? 1 : -1;
                }
        });

        // actual highlighting
        if (newest) {
            for (int j = 0; j < pio_age_list.size() && j < max_age; ++j) {
                PIO_age pair = pio_age_list.get(j);
                if (!pair.active) {
                    continue;
                }

                while (j+1 < pio_age_list.size() && pio_age_list.get(j+1).get_pio().equals(pair.get_pio())) {
                    pair = pio_age_list.get(j+1);
                    pio_age_list.remove(j);
                }

                Color color = computeColorForAge(max_age, j);
                ImmutableList<Integer> pfp = ipt.pathForPosition(pair.get_pio(), filter);
                if (pfp != null) {
                    Range r = ipt.rangeForPath(pfp);
                    Range newR = new Range(r.start() + 1, r.end() + 1); // Off-by-one: siehe updateUpdateHighlights bzw in InnerNodeView. rangeForPath ist schuld
                    Object tag = getColorHighlight(color);
                    paintHighlight(newR, tag);
                }
            }
        } else {
            for (PIO_age pair : pio_age_list) {
                if (!pair.active || pair.get_age() > max_age) {
                    continue;
                }
                PosInOccurrence pio = pair.get_pio();
                Color color = computeColorForAge(max_age, pair.get_age());
                ImmutableList<Integer> pfp = ipt.pathForPosition(pio, filter);
                if (pfp != null) {
                    Range r = ipt.rangeForPath(pfp);
                    Range newR = new Range(r.start() + 1, r.end() + 1); // Off-by-one: siehe updateUpdateHighlights bzw in InnerNodeView. rangeForPath ist schuld
                    Object tag = getColorHighlight(color);
                    paintHighlight(newR, tag);
                }
            }
        }
    }

    /**
     * computes the appropriate color for a given age and maximum age.
     * Implements linear interpolation of the opacity of the color starting at default opacity.
     * @param max_age the maximum age of a term / sf, specified in viewsettings
     * @param age the age of the given term / sf
     * @return the color, with interpolated opacity
     */
    private Color computeColorForAge(int max_age, int age) {
        float[] color = HEATMAP_COLOR.get().getRGBColorComponents(null);
        float alpha = HEATMAP_DEFAULT_START_OPACITY *(1- (float) age/max_age);

        return new Color(color[0], color[1], color[2], alpha);
    }

    /**
     * computes the age of a given sequent formula, i.e.,
     * its distance to the root of the proof tree. If the formula is older
     * than max_age, we do not care, because this method is only used for
     * heatmap highlighting, and older formulas are not considered anyway.
     * @param node the current node
     * @param form the given sf
     * @param max_age the maximum age, specified in viewSettings
     * @return the sf's age
     */
    private int computeSeqFormulaAge(Node node, SequentFormula form, int max_age) {
        int age = -1;
        while (age < max_age && node != null && node.sequent().contains(form)) {
            age++;
            node = node.parent();
        }
        return age;
    }

    public abstract void printSequent();

	public void setFilter(SequentPrintFilter sequentPrintFilter) {
		this.filter = sequentPrintFilter;
		Node selectedNode = getMainWindow().getMediator().getSelectedNode();
		if (selectedNode != null) {
		    // bugfix #1458 (gitlab). The selected node may be null if no proof.
		    this.filter.setSequent(selectedNode.sequent());
		}
		printSequent();

		if (getParent() != null) {
	        getParent().revalidate();
		}
	}

    protected SequentPrintFilter getFilter() {
        return filter;
    }

    /**
     * To update the enclosing components that might print a warning on hidden
     * formulas, it suffices to repaint them.
     */
    protected void updateHidingProperty() {
        updateUI();
        if (getParent() != null) {
            getParent().repaint();
        }
    }

    /**
     * Does this component hide formulas from the sequent due to the set search
     * bar filter
     *
     * @return true iff at least one formula is not shown
     */
    public boolean isHiding() {
        if (filter == null) {
            return false;
        }

        Sequent originalSequent = filter.getOriginalSequent();
        if (originalSequent == null) {
            return false;
        }

        int orgSize = originalSequent.size();
        int newSize = filter.getFilteredAntec().size() + filter.getFilteredSucc().size();
        return orgSize != newSize;
    }

    /**
     *
     * @return {@code true} if this sequent view is supposed to be shown in the {@link MainFrame},
     *  {@code false} if it is only supposed to be shown in some other frame.
     */
    public boolean isMainSequentView() {
        return true;
    }

    /**
     * Utility class consisting of a pair of the PosInOccurrence of a term, and its age.
     * Used for term heatmap highlighting.
     * @author jschiffl
     *
     */
    class PIO_age {
        PosInOccurrence pio;
        int age;
        boolean active = true;
        public PIO_age(PosInOccurrence pio, int age) {
            this.pio = pio;
            this.age = age;
        }
        public PosInOccurrence get_pio() {
            return pio;
        }
        public int get_age() {
            return age;
        }
        public void set_pio(PosInOccurrence pio) {
            this.pio = pio;

        }
        @Override
        public String toString() {
            return "PIO_age [pio=" + pio + ", age=" + age + ", active=" + active + "]";
        }

        @Override
        public boolean equals(Object o) {
            if (o instanceof CurrentGoalView.PIO_age) {
                CurrentGoalView.PIO_age c = (CurrentGoalView.PIO_age) o;
                if (this.age == c.age && this.pio == c.pio) {
                    return true;
                }
            }
            return false;
        }
    }
}
