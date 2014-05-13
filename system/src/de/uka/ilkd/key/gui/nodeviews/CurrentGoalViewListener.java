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

import java.awt.Point;
import java.awt.dnd.DragGestureEvent;
import java.awt.dnd.DragGestureListener;
import java.awt.dnd.DragSource;
import java.awt.dnd.DragSourceAdapter;
import java.awt.dnd.DragSourceDropEvent;
import java.awt.dnd.InvalidDnDOperationException;
import java.awt.event.MouseEvent;

import javax.swing.JLabel;
import javax.swing.JPopupMenu;
import javax.swing.SwingUtilities;
import javax.swing.event.PopupMenuEvent;
import javax.swing.event.PopupMenuListener;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.gui.macros.ProofMacroMenu;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.rule.BuiltInRule;
import java.awt.event.MouseListener;

/**
 * reacts on mouse events to highlight the selected part of the sequent and it
 * pops up a menu showing all applicable Taclet at the highlighted position if
 * the mouse is pressed
 *
 * Additionally it performs all necessary actions for draging some highlighted
 * sequent part into some other GUI component (e.g. some Taclet rule
 * instantiation dialog)
 */
class CurrentGoalViewListener
        implements MouseListener, DragGestureListener {

    private static final int POPUP_DELAY = 400;
    private final KeYMediator mediator;
    private final CurrentGoalView currentGoalView;

    private TacletMenu menu;
    private boolean modalDragNDropEnabled;

    /**
     * hack to block a click event
     */
    private long block = 0;

    CurrentGoalViewListener(final CurrentGoalView currentGoalView, final KeYMediator mediator) {
        this.mediator = mediator;
        this.currentGoalView = currentGoalView;
        menu = new TacletMenu();
        setModalDragNDropEnabled(false);
    }

    @Override
    public void mouseExited(MouseEvent me) {
    }

    @Override
    public void mouseClicked(MouseEvent me) {
        if (!modalDragNDropEnabled()) {
            // if a popup menu is cancelled by a click we do not want to 
            // activate another using the same click event 
            if (Math.abs(System.currentTimeMillis() - block) >= POPUP_DELAY) {
                PosInSequent mousePos = currentGoalView.getPosInSequent(me.getPoint());
                boolean macroActive = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().isRightClickMacro();
                if (mediator != null && mousePos != null) {
                    if (me.isShiftDown()) {
                        if (mediator.getInteractiveProver() != null) {
                            mediator.getInteractiveProver().
                                    startFocussedAutoMode(mousePos.getPosInOccurrence(),
                                    mediator.getSelectedGoal());
                        }
                    } else if (macroActive && SwingUtilities.isRightMouseButton(me)) {
                        ProofMacroMenu macroMenu = new ProofMacroMenu(mediator,
                                mousePos.getPosInOccurrence());
                        if (macroMenu.isEmpty()) {
                            macroMenu.add(new JLabel("no strategies available"));
                        }
                        JPopupMenu popupMenu = macroMenu.getPopupMenu();
                        popupMenu.setLabel("Strategy macros");
                        popupMenu.show(currentGoalView, me.getX() - 5, me.getY() - 5);
                    } else {
                        //done before collecting the taclets because initialising 
                        //built in rules may have side effects on the set of applicable
                        //taclets
                        final ImmutableList<BuiltInRule> builtInRules
                                = mediator.getBuiltInRule(mousePos.getPosInOccurrence());

                        menu = new TacletMenu(currentGoalView,
                                mediator.getFindTaclet(mousePos),
                                mediator.getRewriteTaclet(mousePos),
                                mediator.getNoFindTaclet(),
                                builtInRules,
                                mousePos);

                        currentGoalView.refreshHighlightning = false;

                        final JPopupMenu popup = menu.getPopupMenu();

                        popup.addPopupMenuListener(new PopupMenuListener() {
                            @Override
                            public void popupMenuCanceled(PopupMenuEvent e) {
                                block = System.currentTimeMillis();
                            }

                            @Override
                            public void popupMenuWillBecomeInvisible(PopupMenuEvent e) {
                                currentGoalView.refreshHighlightning = true;
                                block = System.currentTimeMillis();
                            }

                            @Override
                            public void popupMenuWillBecomeVisible(PopupMenuEvent e) {
                                currentGoalView.refreshHighlightning = false;
                            }
                        });

                        popup.show(currentGoalView, me.getX() - 5, me.getY() - 5);
                        popup.requestFocusInWindow();
                    }
                } else {
                    hideMenu();
                    currentGoalView.highlight(me.getPoint());
                }
            } else {
                currentGoalView.highlight(me.getPoint());
            }
        }
    }

    @Override
    public void mousePressed(MouseEvent me) {
    }

    @Override
    public void mouseReleased(MouseEvent me) {
        if (!modalDragNDropEnabled() && menu.isPopupMenuVisible()
                && !menu.getPopupMenu().contains(me.getX() - menu.getX(),
                me.getY() - menu.getY())) {
            hideMenu();
        }
    }

    @Override
    public void mouseEntered(MouseEvent me) {
    }

    public void hideMenu() {
        menu.setPopupMenuVisible(false);
    }

    public final synchronized void setModalDragNDropEnabled(boolean allowDragNDrop) {
        modalDragNDropEnabled = allowDragNDrop;
    }

    public synchronized boolean modalDragNDropEnabled() {
        return modalDragNDropEnabled;
    }

    /**
     * a drag gesture has been initiated
     */
    @Override
    public void dragGestureRecognized(DragGestureEvent dgEvent) {
        final Object oldHighlight = currentGoalView.getCurrentHighlight();
        currentGoalView.setCurrentHighlight(currentGoalView.dndHighlight);
        hideMenu();
        Point dragOrigin = dgEvent.getDragOrigin();
        PosInSequent localMousePos = currentGoalView.getPosInSequent(dragOrigin);

        if (localMousePos != null) {
            try {
                currentGoalView.getDragSource().
                        startDrag(dgEvent,
                        DragSource.DefaultCopyDrop,
                        new PosInSequentTransferable(localMousePos,
                        mediator.getServices()),
                        new DragSourceAdapter() {
                            @Override
                            public void dragDropEnd(DragSourceDropEvent event) {
                                // Enable updating the subterm 
                                // highlightning ...
                                currentGoalView.disableHighlight(currentGoalView.dndHighlight);
                                currentGoalView.setCurrentHighlight(oldHighlight);
                            }
                        });
            } catch (InvalidDnDOperationException dnd) {
                // system not in proper dnd state
                // Enable updating the subterm 
                // highlightning ...
                currentGoalView.disableHighlight(currentGoalView.dndHighlight);
                currentGoalView.setCurrentHighlight(oldHighlight);
            }
        }
    }

}