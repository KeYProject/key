/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.sourceview;

import java.awt.event.ActionEvent;
import javax.swing.AbstractAction;
import javax.swing.Action;
import javax.swing.JComponent;
import javax.swing.JSplitPane;
import javax.swing.JTabbedPane;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.utilities.ClosableTabComponent;

/**
 * This frame contains the {@link SourceView}. Other components may be added in a
 * {@link JTabbedPane} below the {@link SourceView} via {@link #addComponent(JComponent)}
 *
 * @author lanzinger
 */
public class SourceViewFrame extends JSplitPane {

    private static final long serialVersionUID = 382427737154314400L;

    /** The source view contained in this frame. */
    private final SourceView sourceView;

    /** The tabbed pane containing the additional components in this frame. */
    private final JTabbedPane tabbedPane;

    /** The size of the divider between {@link #sourceView} and {@link #tabbedPane}. */
    private final int dividerSize;

    /** Whether {@link #tabbedPane} is currently being shown. */
    private boolean tabbedPaneShown;

    /**
     * Creates a new {@code SourceViewFrame}
     *
     * @param mainWindow the main window.
     */
    public SourceViewFrame(MainWindow mainWindow) {
        super(JSplitPane.VERTICAL_SPLIT);

        sourceView = SourceView.getSourceView(mainWindow);
        tabbedPane = new JTabbedPane();

        setResizeWeight(1);
        setOneTouchExpandable(true);

        setLeftComponent(sourceView);
        setRightComponent(tabbedPane);

        dividerSize = getDividerSize();

        hideTabbedPane();
    }

    private void hideTabbedPane() {
        tabbedPaneShown = false;

        setDividerLocation(1.0);
        setDividerSize(0);
    }

    private void showTabbedPane() {
        tabbedPaneShown = true;

        setDividerLocation(0.5);
        setDividerSize(dividerSize);
    }

    /**
     * Adds a component to be shown below the source view.
     *
     * @param component the component to be shown.
     */
    public void addComponent(JComponent component) {
        addComponent(component, null, new AbstractAction() {

            private static final long serialVersionUID = -3905660332423077705L;

            @Override
            public void actionPerformed(ActionEvent e) {
                removeComponent(component);
            }
        });
    }

    /**
     * <p>
     * Selects the tab containing the specified component.
     * </p>
     *
     * <p>
     * If this frame does not contain the specified component, this method has no effect.
     * </p>
     *
     * @param component the component to select.
     *
     * @throws IllegalArgumentException if this frame does not contain the specified component.
     */
    public void toFront(JComponent component) throws IllegalArgumentException {
        tabbedPane.setSelectedComponent(component);
    }

    /**
     * Adds a component to be shown below the source view.
     *
     * @param component the component to be shown.
     * @param toolTipText the tool tip text for the new tab.
     * @param closeAction the action to perform when the tab is closed.
     */
    public void addComponent(JComponent component, String toolTipText, Action closeAction) {
        tabbedPane.add(component);
        tabbedPane.setTabComponentAt(tabbedPane.indexOfComponent(component),
            new ClosableTabComponent(component.getName(), closeAction));

        tabbedPane.setToolTipTextAt(tabbedPane.indexOfComponent(component), toolTipText);

        if (!tabbedPaneShown) {
            showTabbedPane();
        }

        toFront(component);
    }

    /**
     * <p>
     * Removes a component from below the source view.
     * </p>
     *
     * <p>
     * If this frame does not contain the specified component, this method has no effect.
     * </p>
     *
     * @param component the component to be removed.
     */
    public void removeComponent(JComponent component) {
        tabbedPane.remove(component);

        synchronized (tabbedPane.getTreeLock()) {
            if (tabbedPaneShown && tabbedPane.getComponentCount() == 1) {
                hideTabbedPane();
            }
        }
    }
}
