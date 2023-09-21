/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.ui;

import java.awt.event.ActionEvent;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;

import org.key_project.slicing.DependencyTracker;
import org.key_project.slicing.graph.GraphNode;

/**
 * Context menu action to display the dependency graph "around" a formula.
 *
 * @author Arne Keller
 */
public class ShowGraphAction extends MainWindowAction {

    private static final long serialVersionUID = -9022480738622934631L;

    /**
     * Dependency tracker to use when generating the graph excerpt.
     */
    private final transient DependencyTracker tracker;

    /**
     * The graph node the dependency graph excerpt is centered around.
     */
    private final transient GraphNode node;

    /**
     * Construct a new action.
     *
     * @param mw main window
     * @param tracker dependency tracker of the active proof
     * @param node the graph node to show a graph around
     */
    public ShowGraphAction(MainWindow mw, DependencyTracker tracker, GraphNode node) {
        super(mw);
        setName("Show dependency graph around this formula");
        this.tracker = tracker;
        this.node = node;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        String text = tracker.exportDotAround(false, false, node);
        new PreviewDialog(MainWindow.getInstance(), text);
    }
}
