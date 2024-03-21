/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching.actions;

import java.awt.event.ActionEvent;
import java.util.HashSet;
import java.util.function.Consumer;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.plugins.caching.CachedProofBranch;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.reference.ClosedBy;

import org.key_project.util.GenericWorker;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class RealizeFromDatabaseAction extends KeyAction {
    private static final Logger LOGGER =
        LoggerFactory.getLogger(RealizeFromDatabaseAction.class);

    private final Node node;
    private final CachedProofBranch cachedProofBranch;
    /**
     * Callback to call after realization is done. May be null.
     */
    private final Consumer<Proof> callback;
    private boolean done = false;

    public RealizeFromDatabaseAction(Node node, Consumer<Proof> callback) {
        this.node = node;
        this.callback = callback;
        this.cachedProofBranch = node.lookup(CachedProofBranch.class);

        setName("Realize external proof reference");
        setMenuPath("Proof Caching");
        setEnabled(node.lookup(CachedProofBranch.class) != null);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        var worker = new GenericWorker<>(this::loadProof,
            this::proofLoaded,
            exc -> {
                LOGGER.warn("failed to load proof ", exc);
                node.deregister(node.lookup(CachedProofBranch.class), CachedProofBranch.class);
                IssueDialog.showExceptionDialog(MainWindow.getInstance(), exc);
            });
        worker.execute();
    }

    private Proof loadProof() throws ProblemLoaderException {
        KeYEnvironment<?> e = KeYEnvironment.load(cachedProofBranch.proofFile.toFile());
        return e.getLoadedProof();
    }

    private void proofLoaded(Proof proof) {
        if (done) {
            return;
        }
        done = true; // only run once
        node.deregister(cachedProofBranch, CachedProofBranch.class);
        proof.setStepIndices();
        var allNodes = proof.root().subtreeIterator();
        while (allNodes.hasNext()) {
            var x = allNodes.next();
            if (x.getStepIndex() == cachedProofBranch.stepIndex) {
                node.register(new ClosedBy(proof, x, new HashSet<>()), ClosedBy.class);
                if (callback != null) {
                    callback.accept(proof);
                }
                return;
            }
        }
    }
}
