/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching;

import java.awt.event.ActionEvent;
import java.util.HashSet;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.reference.ClosedBy;

public class RealizeFromDatabaseAction extends KeyAction {
    private final KeYMediator mediator;
    private final Node node;
    private final CachedProofBranch cachedProofBranch;
    /**
     * Callback to call after realization is done. May be null.
     */
    private final Runnable callback;
    private boolean done = false;

    public RealizeFromDatabaseAction(KeYMediator mediator, Node node, Runnable callback) {
        this.mediator = mediator;
        this.node = node;
        this.callback = callback;
        this.cachedProofBranch = node.lookup(CachedProofBranch.class);

        setName("Realize external proof reference");
        setMenuPath("Proof Caching");
        setEnabled(node.lookup(CachedProofBranch.class) != null);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        var proofToLoad = cachedProofBranch.proofFile;
        mediator.registerProofInitializedListener(this::proofLoaded);
        mediator.getUI().loadProblem(proofToLoad);
    }

    private void proofLoaded(Proof proof) {
        if (done) {
            mediator.deregisterProofInitializedListener(this::proofLoaded);
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
                    callback.run();
                }
                return;
            }
        }
    }
}
