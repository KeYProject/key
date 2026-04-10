/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.*;
import java.awt.event.KeyEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import javax.swing.*;
import javax.swing.border.EmptyBorder;
import javax.swing.event.AncestorEvent;
import javax.swing.event.AncestorListener;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.CopyToClipboardAction;

/**
 * Central part of MainWindow. Its main purpose is to serve as container for SequentView instances.
 *
 * @author Kai Wallisch
 */
public final class MainFrame extends JPanel {

    private static final long serialVersionUID = -2412537422601138379L;

    private final JScrollPane scrollPane = new JScrollPane();
    private SequentView sequentView;
    private boolean showTacletInfo = false;

    public void setSequentView(SequentView component) {
        SequentView oldSequentView = sequentView;
        sequentView = component;
        if (component != null) {
            Point oldSequentViewPosition = scrollPane.getViewport().getViewPosition();
            scrollPane.setViewportView(new SequentViewPanel(component));
            scrollPane.getViewport().setViewPosition(oldSequentViewPosition);

            setShowTacletInfo(showTacletInfo);
        } else {
            scrollPane.setViewportView(component);
        }

        if (oldSequentView != null) {
            oldSequentView.removeUserSelectionHighlight();
        }

    }

    public MainFrame(final MainWindow mainWindow, EmptySequent emptySequent) {
        setBorder(new EmptyBorder(0, 0, 0, 0));
        scrollPane.getVerticalScrollBar().setUnitIncrement(30);
        scrollPane.getHorizontalScrollBar().setUnitIncrement(30);

        addMouseListener(new MouseAdapter() {

            @Override
            public void mouseClicked(MouseEvent e) {
                if (sequentView != null) {
                    for (MouseListener listener : sequentView.getMouseListeners()) {
                        if (listener instanceof SequentViewInputListener) {
                            listener.mouseClicked(e);
                        }
                    }
                }
            }
        });

        addAncestorListener(new AncestorListener() {

            @Override
            public void ancestorRemoved(AncestorEvent event) {
                if (sequentView != null) {
                    sequentView.removeUserSelectionHighlight();
                }
            }

            @Override
            public void ancestorMoved(AncestorEvent event) {}

            @Override
            public void ancestorAdded(AncestorEvent event) {}
        });

        // FIXME put this somewhere descent
        getInputMap(WHEN_IN_FOCUSED_WINDOW).put(KeyStroke.getKeyStroke(KeyEvent.VK_C,
            Toolkit.getDefaultToolkit().getMenuShortcutKeyMaskEx()), "copy");
        getActionMap().put("copy", new CopyToClipboardAction(mainWindow));
        setLayout(new BorderLayout());
        add(scrollPane);
        setSequentView(emptySequent);
    }

    public void setShowTacletInfo(boolean showTacletInfo) {
        this.showTacletInfo = showTacletInfo;

        if (sequentView instanceof InnerNodeView view) {
            view.makeTacletInfoVisible(this.showTacletInfo);
        }
    }

    public boolean isShowTacletInfo() {
        return showTacletInfo;
    }

    /**
     * Scroll the sequent view to the specified y coordinate.
     *
     * @param y coordinate in pixels
     */
    public void scrollTo(int y) {
        scrollPane.getVerticalScrollBar().setValue(y);
    }

    public SequentView getSequentView() {
        return sequentView;
    }
}
