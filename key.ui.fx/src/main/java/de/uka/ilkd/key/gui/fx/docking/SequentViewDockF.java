/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.docking;

import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.gui.fx.nodeviews.SequentViewF;
import de.uka.ilkd.key.proof.Node;

/**
 * D34 (P3c): JavaFX port of the Swing {@code SequentViewDock}
 * (key.ui/.../gui/nodeviews/SequentViewDock.java) — a dockable showing the sequent of one
 * arbitrary proof <em>node</em> in a separate buffer (tab), opened by the proof tree popup's
 * "Open Node in Separate Buffer" entry.
 * <ul>
 * <li>the {@link SequentViewF} is created fresh per node and immediately prints the node's
 * sequent (Swing constructor: {@code InnerNodeView} + {@code printSequent()});</li>
 * <li>the title is {@code "Node: " + node.serialNr()} (Swing {@code setTitleText});</li>
 * <li>the tab context menu carries the title action "Jump into Tree" (Swing
 * {@code JumpIntoTreeAction} added via {@code addAction}): the given {@code jumpIntoTree}
 * callback switches the main selection back to this node (wired by {@code MainWindowF}, which
 * owns the selection model).</li>
 * </ul>
 */
public final class SequentViewDockF extends SimpleDockable {

    private final SequentViewF sequentView;

    /** D34: callback selecting this node in the main proof tree (Swing JumpIntoTreeAction). */
    private final Runnable jumpIntoTree;

    /**
     * Creates the dockable for the given proof node.
     *
     * @param node the proof node whose sequent is shown
     * @param jumpIntoTree callback selecting the node in the main proof tree (Swing
     *        {@code JumpIntoTreeAction.actionPerformed}: switch the selection to this node,
     *        switching the proof first if needed)
     */
    public SequentViewDockF(Node node, Runnable jumpIntoTree) {
        super("node-buffer-" + node.serialNr(), "Node: " + node.serialNr(),
            new SequentViewF());
        this.sequentView = (SequentViewF) getContent();
        this.jumpIntoTree = Objects.requireNonNull(jumpIntoTree);
        sequentView.display(node);
        sequentView.printSequent();
    }

    @Override
    public List<DockTitleActionF> getTitleActions() {
        return List.of(new DockTitleActionF("Jump into Tree", jumpIntoTree));
    }

    /**
     * @return the node displaying the sequent buffer (self test)
     */
    public SequentViewF getSequentView() {
        return sequentView;
    }
}
