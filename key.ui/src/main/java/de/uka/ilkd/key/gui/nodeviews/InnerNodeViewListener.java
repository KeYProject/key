/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.event.MouseEvent;
import javax.swing.SwingUtilities;

import de.uka.ilkd.key.pp.PosInSequent;

/**
 * Listener for an {@link InnerNodeView}
 *
 * Reacts on mouse events to highlight the selected part of the sequent and it pops up a menu
 * showing all applicable actions at the highlighted position.
 */
public class InnerNodeViewListener extends SequentViewListener<InnerNodeView> {

    /** The menu shown on a mouse click. */
    private InnerNodeViewMenu menu;

    /**
     * Creates a new listener.
     *
     * @param innerNodeView an {@code InnerNodeView}.
     */
    InnerNodeViewListener(final InnerNodeView innerNodeView) {
        super(innerNodeView);
        menu = new InnerNodeViewMenu();
    }

    @Override
    public void mouseClicked(MouseEvent me) {
        if (Math.abs(System.currentTimeMillis() - getLastPopupCloseTime()) >= POPUP_DELAY) {
            PosInSequent mousePos = getSequentView().getPosInSequent(me.getPoint());
            if (mousePos != null) {
                if (!me.isShiftDown() && !me.isControlDown()
                        && SwingUtilities.isLeftMouseButton(me)) {
                    menu = new InnerNodeViewMenu(getSequentView(), mousePos);
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

    @Override
    public void mouseExited(MouseEvent me) {}

    @Override
    public void mousePressed(MouseEvent e) {}

    @Override
    public void mouseReleased(MouseEvent e) {}

    @Override
    public void mouseEntered(MouseEvent e) {}
}
