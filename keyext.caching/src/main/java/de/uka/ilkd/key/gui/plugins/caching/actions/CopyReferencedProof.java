/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching.actions;

import java.awt.event.ActionEvent;
import java.util.HashSet;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.plugins.caching.CachedProofBranch;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.reference.ClosedBy;
import de.uka.ilkd.key.proof.replay.CopyingProofReplayer;

import org.key_project.util.GenericWorker;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Action to copy referenced proof steps to the new proof.
 *
 * @author Arne Keller
 */
public final class CopyReferencedProof extends KeyAction {
    private static final Logger LOGGER = LoggerFactory.getLogger(CopyReferencedProof.class);

    /**
     * The mediator.
     */
    private final KeYMediator mediator;
    /**
     * The node to copy the steps to.
     */
    private final Node node;

    /**
     * Construct a new action.
     *
     * @param mediator the mediator
     * @param node the node
     */
    public CopyReferencedProof(KeYMediator mediator, Node node) {
        this.mediator = mediator;
        this.node = node;
        setName("Copy referenced proof steps here");
        setEnabled(node.leaf() && node.isClosed()
                && (node.lookup(ClosedBy.class) != null
                        || node.lookup(CachedProofBranch.class) != null));
        setMenuPath("Proof Caching");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        mediator.stopInterface(true);
        // first, load the external proof
        CachedProofBranch cachedProofBranch = node.lookup(CachedProofBranch.class);
        node.deregister(cachedProofBranch, CachedProofBranch.class);
        if (cachedProofBranch != null) {
            var worker = new GenericWorker<>(
                () -> KeYEnvironment.load(cachedProofBranch.proofFile.toFile()).getLoadedProof(),
                proof -> {
                    proof.setStepIndices();
                    var allNodes = proof.root().subtreeIterator();
                    while (allNodes.hasNext()) {
                        var x = allNodes.next();
                        if (x.getStepIndex() == cachedProofBranch.stepIndex) {
                            node.register(new ClosedBy(proof, x, new HashSet<>()), ClosedBy.class);
                            actionPerformed(null);
                            return;
                        }
                    }
                },
                exc -> {
                    LOGGER.warn("failed to load proof ", exc);
                    IssueDialog.showExceptionDialog(MainWindow.getInstance(), exc);
                });
            worker.execute();
            return;
        }
        // then, do any internal work
        ClosedBy c = node.lookup(ClosedBy.class);
        node.deregister(c, ClosedBy.class);
        Goal current = node.proof().getClosedGoal(node);
        try {
            new CopyingProofReplayer(c.proof(), node.proof()).copy(c.node(), current,
                c.nodesToSkip());
            // dispose old proof if it isn't loaded in the UI
            if (!mediator.getCurrentlyOpenedProofs().contains(c.proof())) {
                c.proof().dispose();
            }
            mediator.startInterface(true);
        } catch (Exception ex) {
            LOGGER.error("failed to copy proof ", ex);
            IssueDialog.showExceptionDialog(MainWindow.getInstance(), ex);
        }
    }
}
