/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.*;
import java.awt.dnd.*;
import java.awt.event.MouseEvent;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.ProofMacroMenu;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.key_project.util.collection.ImmutableList;

/**
 * Listener for a {@link CurrentGoalView}.
 *
 * Reacts on mouse events to highlight the selected part of the sequent and it pops up a menu
 * showing all applicable actions and rules at the highlighted position.
 *
 * Additionally it performs all necessary actions for draging some highlighted sequent part into
 * some other GUI component (e.g. some Taclet rule instantiation dialog)
 */
final class CurrentGoalViewListener extends SequentViewListener<CurrentGoalView>
        implements DragGestureListener {

    private final KeYMediator mediator;

    private CurrentGoalViewMenu menu;
    private boolean modalDragNDropEnabled;

    CurrentGoalViewListener(final CurrentGoalView currentGoalView, final KeYMediator mediator) {
        super(currentGoalView);
        this.mediator = mediator;
        menu = new CurrentGoalViewMenu();
        setModalDragNDropEnabled(false);
    }

    @Override
    public void mouseExited(MouseEvent me) {
    }

    @Override
    public void mouseClicked(MouseEvent me) {
        if (!modalDragNDropEnabled()) {
            if (Math.abs(System.currentTimeMillis() - getLastPopupCloseTime()) >= POPUP_DELAY) {
                PosInSequent mousePos = getSequentView().getPosInSequent(me.getPoint());
                boolean macroActive = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()
                        .isRightClickMacro();
                if (mediator != null && mousePos != null) {
                    if (me.isShiftDown()) {
                        mediator.getUI().getProofControl().startFocussedAutoMode(
                            mousePos.getPosInOccurrence(), mediator.getSelectedGoal());
                    } else if (macroActive && SwingUtilities.isRightMouseButton(me)) {
                        ProofMacroMenu macroMenu =
                            new ProofMacroMenu(mediator, mousePos.getPosInOccurrence());
                        if (macroMenu.isEmpty()) {
                            macroMenu.add(new JLabel("No strategies available"));
                        }
                        JPopupMenu popupMenu = macroMenu.getPopupMenu();
                        popupMenu.setLabel("Strategy Macros");
                        popupMenu.show(getSequentView(), me.getX() - 5, me.getY() - 5);
                    } else if (!me.isControlDown() && SwingUtilities.isLeftMouseButton(me)) {
                        // done before collecting the taclets because initialising
                        // built in rules may have side effects on the set of applicable
                        // taclets
                        final ImmutableList<BuiltInRule> builtInRules =
                            mediator.getUI().getProofControl().getBuiltInRule(
                                mediator.getSelectedGoal(), mousePos.getPosInOccurrence());

                        menu = new CurrentGoalViewMenu(getSequentView(),
                            mediator.getUI().getProofControl().getFindTaclet(
                                mediator.getSelectedGoal(), mousePos.getPosInOccurrence()),
                            mediator.getUI().getProofControl().getRewriteTaclet(
                                mediator.getSelectedGoal(), mousePos.getPosInOccurrence()),
                            mediator.getUI().getProofControl().getNoFindTaclet(
                                mediator.getSelectedGoal()),
                            builtInRules, mousePos);

                        showPopup(me, menu);
                    }
                } else {
                    hideMenu(menu);
                    getSequentView().highlight(me.getPoint());
                }
            } else {
                getSequentView().highlight(me.getPoint());
            }
        }
    }

    @Override
    public void mousePressed(MouseEvent me) {
    }

    @Override
    public void mouseReleased(MouseEvent me) {
        if (!modalDragNDropEnabled() && menu.isPopupMenuVisible() && !menu.getPopupMenu()
                .contains(me.getX() - menu.getX(), me.getY() - menu.getY())) {
            hideMenu(menu);
        }
    }

    @Override
    public void mouseEntered(MouseEvent me) {
    }

    public synchronized void setModalDragNDropEnabled(boolean allowDragNDrop) {
        modalDragNDropEnabled = allowDragNDrop;
    }

    public synchronized boolean modalDragNDropEnabled() {
        return modalDragNDropEnabled;
    }

    @Override
    public void dragGestureRecognized(DragGestureEvent dgEvent) {
        final Object oldHighlight = getSequentView().getCurrentHighlight();
        getSequentView().setCurrentHighlight(getSequentView().dndHighlight);
        hideMenu(menu);
        Point dragOrigin = dgEvent.getDragOrigin();
        PosInSequent localMousePos = getSequentView().getPosInSequent(dragOrigin);

        if (localMousePos != null) {
            try {
                getSequentView().getDragSource().startDrag(dgEvent, DragSource.DefaultCopyDrop,
                    new PosInSequentTransferable(localMousePos, mediator.getServices()),
                    new DragSourceAdapter() {
                        @Override
                        public void dragDropEnd(DragSourceDropEvent event) {
                            // Enable updating the subterm
                            // highlightning ...
                            getSequentView().disableHighlight(getSequentView().dndHighlight);
                            getSequentView().setCurrentHighlight(oldHighlight);
                        }
                    });
            } catch (InvalidDnDOperationException dnd) {
                // system not in proper dnd state
                // Enable updating the subterm
                // highlightning ...
                getSequentView().disableHighlight(getSequentView().dndHighlight);
                getSequentView().setCurrentHighlight(oldHighlight);
            }
        }
    }

}
