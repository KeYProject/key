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
import java.util.EventObject;
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
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.pp.SequentPrintFilter;
import de.uka.ilkd.key.pp.SequentPrintFilterEntry;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
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
    private static final Color HEATMAP_DEFAULT_COLOR = new Color(.7f, .5f, .5f);
    // maximum age of a sequent formula for heatmap
    public static final int MAX_AGE = 6;

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
    
    private void updateHeatmapHighlights() {
        if (getLogicPrinter() == null) {
            return;
        }
        
        heatMapHighlights.clear();

        InitialPositionTable ipt = getLogicPrinter().getInitialPositionTable();
        
        int i = 0;
        
        ImmutableList<SequentPrintFilterEntry> entryList = filter.getFilteredAntec().append(filter.getFilteredSucc());
        
        for(SequentPrintFilterEntry entry : entryList) {
            SequentFormula form = entry.getFilteredFormula();
            int age = computeSeqFormulaAge(getMainWindow().getMediator().getSelectedNode(), form);
            if(age < MAX_AGE) {
                Color color = computeColorForAge(age);
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

    private Color computeColorForAge(int age) {
        float[] color = HEATMAP_DEFAULT_COLOR.getRGBColorComponents(null);
        float redDiff = (1.f - color[0]);
        float greenDiff = (1.f - color[1]);
        float blueDiff = (1.f - color[2]);
        // exponentieller abfall - unterschiede zwischen ersten zwei, drei formeln deutlicher, danach kaum noch unterschied
        // float diff = (float) (1.f - Math.pow(.5f, age-1)); 
        
        // linearer abfall
        float diff = (float) age / MAX_AGE;
        float red = color[0] + redDiff * diff;
        float green = color[1] + greenDiff * diff;
        float blue = color[2] + blueDiff * diff;
        return new Color(red, green, blue);
    }

    private int computeSeqFormulaAge(Node node, SequentFormula form) {
        int age = 0;
        while (age < MAX_AGE && node != null && node.sequent().contains(form)) {
            age++;
            node = node.parent();
        }
        return age;
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
            getLogicPrinter().update(filter, getLineWidth());
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
        if (ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().heatmapEnabled()) {
            updateHeatmapHighlights();
        }
        restorePosition();
        addMouseListener(listener);
        repaint();
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
        filter.setSequent(goal.sequent());
        setLogicPrinter(new SequentViewLogicPrinter(new ProgramPrinter(null),
                                                    getMediator().getNotationInfo(),
                                                    mediator.getServices(),
                                                    getVisibleTermLabels()));
    }

    protected SequentPrintFilter getSequentPrintFilter() {
        return filter;
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