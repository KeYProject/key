/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.*;
import java.awt.dnd.Autoscroll;
import java.awt.dnd.DnDConstants;
import java.awt.dnd.DragSource;
import java.awt.dnd.DropTarget;
import java.util.EventObject;
import java.util.LinkedList;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.ApplyTacletDialog;
import de.uka.ilkd.key.gui.GUIListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.pp.InitialPositionTable;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.Debug;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This sequent view displays the sequent of an open goal and allows selection of formulas as well
 * as the application of rules. It offers services for highlighting formulas, selecting applicable
 * rules (in particular taclets) and drag'n drop instantiation of taclets.
 */
public final class CurrentGoalView extends SequentView implements Autoscroll {

    /**
     *
     */
    private static final long serialVersionUID = 8494000234215913553L;

    public static final ColorSettings.ColorProperty DEFAULT_HIGHLIGHT_COLOR =
        ColorSettings.define("[currentGoal]defaultHighlight", "", new Color(70, 100, 170, 76));

    public static final ColorSettings.ColorProperty ADDITIONAL_HIGHLIGHT_COLOR =
        ColorSettings.define("[currentGoal]addtionalHighlight", "", new Color(0, 0, 0, 38));

    private static final ColorSettings.ColorProperty UPDATE_HIGHLIGHT_COLOR =
        ColorSettings.define("[currentGoal]updateHighlight", "", new Color(0, 150, 130, 38));

    public static final ColorSettings.ColorProperty DND_HIGHLIGHT_COLOR =
        ColorSettings.define("[currentGoal]dndHighlight", "", new Color(0, 150, 130, 104));

    private static final Logger LOGGER = LoggerFactory.getLogger(CurrentGoalView.class);


    // the mediator
    private final KeYMediator mediator;

    // the mouse/mouseMotion listener
    private final CurrentGoalViewListener listener;

    // enables this component to be a Drag Source
    private final DragSource dragSource;

    private static final Insets autoScrollSensitiveRegion = new Insets(20, 20, 20, 20);

    private final LinkedList<Object> updateHighlights;

    /**
     * creates a viewer for a sequent
     *
     * @param mainWindow the MainWindow allowing access to the current system status
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

        updateHighlights = new LinkedList<>();

    }

    /**
     * updates all updateHighlights. Firstly removes all displayed ones and then gets a new list of
     * updates to highlight
     */
    void updateUpdateHighlights() {
        if (getLogicPrinter() == null) {
            return;
        }

        for (Object updateHighlight : updateHighlights) {
            removeHighlight(updateHighlight);
        }

        updateHighlights.clear();
        InitialPositionTable ipt = getInitialPositionTable();
        Range[] ranges = ipt.getUpdateRanges();

        if (ranges != null) {
            for (Range range : ranges) {
                // NOTE (DS): The below addition of 1 to the beginning is a quick-and-dirty
                // fix for a shift of highlighted areas to the left that occurred after the
                // change to HTML documents in the JEditorPane (previous JTextArea). If
                // something concerning highlighting does not work in the future, here could
                // be a starting place to find the mistake.
                range = new Range(range.start() + 1, range.end() + 1);

                Object tag = getColorHighlight(UPDATE_HIGHLIGHT_COLOR.get());
                updateHighlights.add(tag);
                paintHighlight(range, tag);
            }
        }
    }

    DragSource getDragSource() {
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
            Runnable sequentUpdater = this::printSequentImmediately;
            SwingUtilities.invokeLater(sequentUpdater);
        }
    }

    /**
     * sets the text being printed
     */
    synchronized void printSequentImmediately() {
        if (getMainWindow().getMediator().getSelectedNode() == null) {
            // only print when a node is selected
            // (avoids NPE when no proof is loaded and font size is changed)
            return;
        }
        var time = System.nanoTime();
        getHighlighter().removeAllHighlights();

        removeMouseListener(listener);

        setLineWidth(computeLineWidth());

        if (getLogicPrinter() != null) {
            updateSequent(getMainWindow().getMediator().getSelectedNode());
        }

        updateUpdateHighlights();
        updateHeatMapHighlights();
        restorePosition();
        addMouseListener(listener);
        updateHidingProperty();
        var after = System.nanoTime();
        LOGGER.trace("Total printSequentImmediately took " + (after - time) / 1e6 + "ms");
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
        setLogicPrinter(SequentViewLogicPrinter.positionPrinter(getMediator().getNotationInfo(),
            mediator.getServices(), getVisibleTermLabels()));
    }

    /**
     * returns the mediator of this view
     *
     * @return the KeYMediator
     */
    public KeYMediator getMediator() {
        return mediator;
    }

    /**
     * selected rule to apply
     *
     * @param taclet the selected Taclet
     * @param pos the PosInSequent describes the position where to apply the rule
     */
    void selectedTaclet(TacletApp taclet, PosInSequent pos) {
        KeYMediator r = getMediator();
        // This method delegates the request only to the UserInterfaceControl which implements the
        // functionality.
        // No functionality is allowed in this method body!
        Goal goal = r.getSelectedGoal();
        Debug.assertTrue(goal != null);
        r.getUI().getProofControl().selectedTaclet(taclet.taclet(), goal, pos.getPosInOccurrence());
    }

    public PosInSequent getMousePosInSequent() {
        return getPosInSequent(getMousePosition());
    }

    /**
     * used for autoscrolling when performing drag and drop actions. Computes the rectangle to be
     * made visible.
     */
    @Override
    public void autoscroll(Point loc) {
        final Insets insets = getAutoscrollInsets();
        final Rectangle outer = getVisibleRect();
        final Rectangle inner = new Rectangle(outer.x + insets.left, outer.y + insets.top,
            outer.width - (insets.left + insets.right),
            outer.height - (insets.top + insets.bottom));

        if (!inner.contains(loc)) {
            Rectangle scrollRect = new Rectangle(loc.x - insets.left, loc.y - insets.top,
                insets.left + insets.right, insets.top + insets.bottom);
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
