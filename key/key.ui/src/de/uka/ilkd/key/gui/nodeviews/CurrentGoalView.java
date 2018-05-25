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

import java.awt.Color;
import java.awt.Insets;
import java.awt.Point;
import java.awt.Rectangle;
import java.awt.dnd.Autoscroll;
import java.awt.dnd.DnDConstants;
import java.awt.dnd.DragSource;
import java.awt.dnd.DropTarget;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.EventObject;
import java.util.Iterator;
import java.util.LinkedList;

import javax.swing.SwingUtilities;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.ApplyTacletDialog;
import de.uka.ilkd.key.gui.GUIListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.pp.InitialPositionTable;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.logic.FormulaChangeInfo;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.pp.SequentPrintFilter;
import de.uka.ilkd.key.pp.SequentPrintFilterEntry;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;
import de.uka.ilkd.key.util.Debug;

/**
 * This sequent view displays the sequent of an open goal and allows selection
 * of formulas as well as the application of rules. It offers services for
 * highlighting formulas, selecting applicable rules (in particular taclets) and
 * drag'n drop instantiation of taclets.
 */
public class CurrentGoalView extends SequentView implements Autoscroll {

    /**
     *
     */
    private static final long serialVersionUID = 8494000234215913553L;

    public static final Color DEFAULT_HIGHLIGHT_COLOR = new Color(70, 100, 170, 76);

    public static final Color ADDITIONAL_HIGHLIGHT_COLOR = new Color(0, 0, 0, 38);

    private static final Color UPDATE_HIGHLIGHT_COLOR = new Color(0, 150, 130, 38);

    public static final Color DND_HIGHLIGHT_COLOR = new Color(0, 150, 130, 104);

    // default starting color for heatmaps
    private static final Color HEATMAP_DEFAULT_START_COLOR = new Color(.8f, .7f, .5f);


    // the mediator
    private final KeYMediator mediator;

    // the mouse/mouseMotion listener
    private final CurrentGoalViewListener listener;

    // enables this component to be a Drag Source
    private DragSource dragSource = null;

    private static final Insets autoScrollSensitiveRegion = new Insets(20, 20, 20, 20);

    private final LinkedList<Object> updateHighlights;
    private final LinkedList<Object> heatMapHighlights;

    /**
     * creates a viewer for a sequent
     *
     * @param mainWindow the MainWindow allowing access to the current system
     * status
     */
    public CurrentGoalView(MainWindow mainWindow) {
        super(mainWindow);
        this.mediator = mainWindow.getMediator();
        setBackground(Color.white);
        // disables selection
        setSelectionColor(getBackground());
        listener = new CurrentGoalViewListener(this, getMediator());

        GUIListener guiListener = new GUIListener() {
            /**
             * invoked if a frame that wants modal access is opened
             */
            @Override
            public void modalDialogOpened(EventObject e) {

                // enable textual DnD in case that the opened model dialog
                // is the ApplyTacletDialog
                final boolean enableDnD = e.getSource() instanceof ApplyTacletDialog;
                listener.setModalDragNDropEnabled(enableDnD);
                refreshHighlightning = enableDnD;

                // disable drag and drop instantiation of taclets
                getDropTarget().setActive(false);
            }

            /**
             * invoked if a frame that wants modal access is closed
             */
            @Override
            public void modalDialogClosed(EventObject e) {
                if (e.getSource() instanceof ApplyTacletDialog) {
                    // disable drag'n'drop ...
                    listener.setModalDragNDropEnabled(false);
                }

                refreshHighlightning = true;

                // enable drag and drop instantiation of taclets
                getDropTarget().setActive(true);
            }

            /**
             * invoked if the user wants to abort the proving session
             */
            @Override
            public void shutDown(EventObject e) {
            }
        };

        addMouseListener(listener);

        // and here comes the drag'n'drop stuff that allows the user to copy
        // the currently highlighted subterm/formula by mere drag'n'dop actions
        dragSource = new DragSource();
        dragSource.createDefaultDragGestureRecognizer(this, DnDConstants.ACTION_COPY, listener);

        // And now the Drag'n'drop stuff ...
        final DragNDropInstantiator dragNDropInstantiator = new DragNDropInstantiator(this);
        final DropTarget aDropTarget = new DropTarget(this, dragNDropInstantiator);

        this.setAutoscrolls(true);
        this.setDropTarget(aDropTarget);

        // add listener to KeY GUI events
        getMediator().addGUIListener(guiListener);

        updateHighlights = new LinkedList<Object>();
        heatMapHighlights   = new LinkedList<Object>();

    }

    /**
     * updates all updateHighlights. Firstly removes all displayed ones and then
     * gets a new list of updates to highlight
     */
    void updateUpdateHighlights() {
        if (getLogicPrinter() == null) {
            return;
        }

        for (Object updateHighlight : updateHighlights) {
            removeHighlight(updateHighlight);
        }

        updateHighlights.clear();
        InitialPositionTable ipt = getLogicPrinter().getInitialPositionTable();
        Range[] ranges = ipt.getUpdateRanges();

        if (ranges != null) {
            for (Range range : ranges) {
                // NOTE (DS): The below addition of 1 to the beginning is a quick-and-dirty
                // fix for a shift of highlighted areas to the left that occurred after the
                // change to HTML documents in the JEditorPane (previous JTextArea). If
                // something concerning highlighting does not work in the future, here could
                // be a starting place to find the mistake.
                range = new Range(range.start() + 1, range.end() + 1);

                Object tag = getColorHighlight(UPDATE_HIGHLIGHT_COLOR);
                updateHighlights.add(tag);
                paintHighlight(range, tag);
            }
        }
    }


    /**
     * Highlights sequent formulas according to their age (if newest is false),
     * or the newest sequent formulas.
     * @param max_age maximum age up to which sf's are highlighted, or number of recent sf's to highlight.
     * @param newest Are newest sf's highlighted (true) or all up to max_age (false)?
     */
    private void updateHeatmapSFHighlights(int max_age, boolean newest) {
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
                    if (o1age > o2age) {
                        return 1;
                    } else if (o1age < o2age) {
                        return -1;
                    } else {
                        return 0;
                    }
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
                        heatMapHighlights.add(tag);
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
                    heatMapHighlights.add(tag);
                    paintHighlight(newR, tag);
                }
                ++i;
            }
        }
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
            if (o instanceof PIO_age) {
                PIO_age c = (PIO_age) o;
                if (this.age == c.age && this.pio == c.pio) {
                    return true;
                }
            }
            return false;
        }
    }


    /**
     * Highlights terms according to their age (if newest is false),
     * or the newest terms.
     * @param max_age maximum age up to which terms are highlighted, or number of recent terms to highlight.
     * @param newest Are newest terms highlighted (true) or all up to max_age (false)?
     */
    private void updateHeatmapTermHighlights(int max_age, boolean newest) {
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
                    heatMapHighlights.add(tag);
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
                    heatMapHighlights.add(tag);
                    paintHighlight(newR, tag);
                }
            }
        }
    }

    /**
     * computes the appropriate color for a given age and maximum age.
     * Implements linear interpolation between the starting colour and white.
     * @param max_age the maximum age of a term / sf, specified in viewsettings
     * @param age the age of the given term / sf
     * @return the appropriate color
     */
    private Color computeColorForAge(int max_age, int age) {
        float[] color = HEATMAP_DEFAULT_START_COLOR.getRGBColorComponents(null);
        float redDiff = (1.f - color[0]);
        float greenDiff = (1.f - color[1]);
        float blueDiff = (1.f - color[2]);
        // exponentieller abfall - unterschiede zwischen ersten zwei, drei formeln deutlicher, danach kaum noch unterschied
        // float diff = (float) (1.f - Math.pow(.5f, age-1));

        // linearer abfall
        float diff = (float) age / max_age;
        float red = color[0] + redDiff * diff;
        float green = color[1] + greenDiff * diff;
        float blue = color[2] + blueDiff * diff;
        return new Color(red, green, blue);
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

    /**
     * given a node and a sequent formula, returns the first node
     * among the node's parents that contains the sequent formula @form.
     */
    public Node jumpToIntroduction(Node node, SequentFormula form) {
        while (node.parent() != null && node.sequent().contains(form)) {
            node = node.parent();
        }
        return node;
    }



    protected DragSource getDragSource() {
        return dragSource;
    }

    /**
     * sets the text being printed
     */
    @Override
    public synchronized void printSequent() {
        if (SwingUtilities.isEventDispatchThread()) {
            printSequentImmediately();
        } else {
            Runnable sequentUpdater = new Runnable() {
                @Override
                public void run() {
                    printSequentImmediately();
                }
            };
            SwingUtilities.invokeLater(sequentUpdater);
        }
    }

    /**
     * sets the text being printed
     */
    synchronized void printSequentImmediately() {
        removeMouseListener(listener);

        setLineWidth(computeLineWidth());

        if (getLogicPrinter() != null) {
            getLogicPrinter().update(getFilter(), getLineWidth());
            boolean errorocc;
            do {
                errorocc = false;
                try {
                    setText(getSyntaxHighlighter().process(
                            getLogicPrinter().toString(),
                            getMainWindow().getMediator().getSelectedNode()));
                } catch (Error e) {
                    System.err.println("Error occurred while printing Sequent!");
                    e.printStackTrace();
                    errorocc = true;
                }
            } while (errorocc);
        }

        updateUpdateHighlights();
        heatMapHighlights.clear();
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
        restorePosition();
        addMouseListener(listener);
        updateHidingProperty();
    }

    // last highlighted caret position
    private int lastHighlightedCaretPos;

    @Override
    public void highlight(Point p) {
        super.highlight(p);
        lastHighlightedCaretPos = correctedViewToModel(p);
    }

    void restorePosition() {
        int lastHighlightedCaretPosTmp = lastHighlightedCaretPos;
        if (!(lastHighlightedCaretPosTmp < 0 || getDocument() == null
                || lastHighlightedCaretPosTmp > getDocument().getLength())) {
            setCaretPosition(lastHighlightedCaretPosTmp);
        }
    }

    /**
     * sets the LogicPrinter to use
     */
    public void setPrinter(Goal goal) {
        getFilter().setSequent(goal.sequent());
        setLogicPrinter(new SequentViewLogicPrinter(new ProgramPrinter(null),
                                                    getMediator().getNotationInfo(),
                                                    mediator.getServices(),
                                                    getVisibleTermLabels()));
    }

    protected SequentPrintFilter getSequentPrintFilter() {
        return getFilter();
    }

    /**
     * returns the mediator of this view
     *
     * @return the KeYMediator
     */
    public final KeYMediator getMediator() {
        return mediator;
    }

    /**
     * selected rule to apply
     *
     * @param taclet the selected Taclet
     * @param pos the PosInSequent describes the position where to apply the
     * rule
     */
    void selectedTaclet(TacletApp taclet, PosInSequent pos) {
        KeYMediator r = getMediator();
      // This method delegates the request only to the UserInterfaceControl which implements the functionality.
        // No functionality is allowed in this method body!
        Goal goal = r.getSelectedGoal();
        Debug.assertTrue(goal != null);
        r.getUI().getProofControl().selectedTaclet(taclet.taclet(), goal, pos.getPosInOccurrence());
    }

    /**
     * Enables drag'n'drop of highlighted subterms in the sequent window.
     *
     * @param allowDragNDrop enables drag'n'drop iff set to true.
     */
    public synchronized void setModalDragNDropEnabled(boolean allowDragNDrop) {
        listener.setModalDragNDropEnabled(allowDragNDrop);
    }

    /**
     * Checks whether drag'n'drop of highlighted subterms in the sequent window
     * currently is enabled..
     *
     * @return true iff drag'n'drop is enabled.
     */
    public synchronized boolean modalDragNDropEnabled() {
        return listener.modalDragNDropEnabled();
    }

    @Override
    public String getHighlightedText() {
        return getHighlightedText(getPosInSequent(getMousePosition()));
    }

    public PosInSequent getMousePosInSequent() {
        return getPosInSequent(getMousePosition());
    }

    /**
     * used for autoscrolling when performing drag and drop actions. Computes
     * the rectangle to be made visible.
     */
    @Override
    public void autoscroll(Point loc) {
        final Insets insets = getAutoscrollInsets();
        final Rectangle outer = getVisibleRect();
        final Rectangle inner = new Rectangle(outer.x + insets.left,
                outer.y + insets.top,
                outer.width - (insets.left + insets.right),
                outer.height - (insets.top + insets.bottom));

        if (!inner.contains(loc)) {
            Rectangle scrollRect = new Rectangle(loc.x - insets.left,
                    loc.y - insets.top, insets.left + insets.right,
                    insets.top + insets.bottom);
            scrollRectToVisible(scrollRect);
        }
    }

    /**
     * used to define the area in which autoscrolling will be initialized
     */
    @Override
    public Insets getAutoscrollInsets() {
        return autoScrollSensitiveRegion;
    }

    @Override
    public String getTitle() {
        return "Current Goal";
    }

}