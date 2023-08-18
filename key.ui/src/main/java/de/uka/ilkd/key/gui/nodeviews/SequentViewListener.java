/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import javax.swing.JMenu;
import javax.swing.JPopupMenu;
import javax.swing.event.PopupMenuEvent;
import javax.swing.event.PopupMenuListener;

/**
 * Listener for a {@link SequentView}.
 *
 * Reacts on mouse events to highlight the selected part of the sequent and it pops up a menu
 * showing all applicable actions at the highlighted position.
 *
 * @param <T> the type of the object this listener is listening to.
 */
abstract class SequentViewListener<T extends SequentView> implements MouseListener {

    /**
     * The delay after closing a popup menu before another menu may be opened.
     */
    public static final int POPUP_DELAY = 400;

    private long lastPopupCloseTime = 0;

    private final T sequentView;

    /**
     * Creates a new listener.
     *
     * @param sequentView a {@code SequentView}
     */
    SequentViewListener(T sequentView) {
        this.sequentView = sequentView;
    }

    /**
     *
     * @return the sequent view this object is listening to.
     */
    public T getSequentView() {
        return sequentView;
    }

    /**
     * Hides the specified menu.
     *
     * @param menu the menu to hide.
     */
    void hideMenu(JMenu menu) {
        menu.setPopupMenuVisible(false);
    }

    /**
     *
     * @return the time at which the last popup was closed.
     * @see SequentViewListener#POPUP_DELAY
     */
    long getLastPopupCloseTime() {
        return lastPopupCloseTime;
    }

    /**
     * Shows a new popup menu at the specified mouse event's position.
     *
     * @param me a mouse event.
     * @param menu the menu to show.
     */
    void showPopup(MouseEvent me, JMenu menu) {
        sequentView.refreshHighlightning = false;

        final JPopupMenu popup = menu.getPopupMenu();

        popup.addPopupMenuListener(new PopupMenuListener() {
            @Override
            public void popupMenuCanceled(PopupMenuEvent e) {
                lastPopupCloseTime = System.currentTimeMillis();
            }

            @Override
            public void popupMenuWillBecomeInvisible(PopupMenuEvent e) {
                sequentView.refreshHighlightning = true;
                lastPopupCloseTime = System.currentTimeMillis();
            }

            @Override
            public void popupMenuWillBecomeVisible(PopupMenuEvent e) {
                sequentView.refreshHighlightning = false;
            }
        });

        popup.show(sequentView, me.getX() - 5, me.getY() - 5);
        popup.requestFocusInWindow();
    }
}
