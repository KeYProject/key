/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.prooftree;

import java.nio.file.Path;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Documents the fail-fast contract of the proof tree model for the constellation behind issue
 * #3713: nodes of a foreign (here: already disposed) proof must never be fed into another proof's
 * {@link GUIProofTreeModel}. The information-flow auto pilot's side proof used to leak into
 * {@code ProofTreeView.modifiedSubtrees} this way; the actual fix prevents the leak in
 * {@code ProofTreeView} and {@code AbstractMediatorUserInterfaceControl#macroFinished}. The model
 * itself deliberately keeps failing fast when the invariant is violated, so that bookkeeping bugs
 * of this kind surface instead of being rendered silently.
 */
public class DisposedProofTreeUpdateTest {
    private static final Path exampleDir = requireExampleDirectory();

    private static Path requireExampleDirectory() {
        Path dir = FindResources.getExampleDirectory();
        if (dir == null) {
            // the example directory must be checked out for these tests to run
            throw new NullPointerException("No example directory available.");
        }
        return dir;
    }

    private static Proof requireProof(KeYEnvironment<DefaultUserInterfaceControl> env,
            String label) {
        Proof proof = env.getLoadedProof();
        if (proof == null) {
            throw new NullPointerException("No loaded proof for " + label + ".");
        }
        return proof;
    }

    private static final String EXAMPLE_PROOF =
        "standard_key/BookExamples/10UsingKeY/andCommutes.proof";

    @Test
    void updatingWithNodeOfForeignDisposedProofFailsFast() throws Exception {
        KeYEnvironment<DefaultUserInterfaceControl> env =
            KeYEnvironment.load(exampleDir.resolve(EXAMPLE_PROOF));
        Proof displayed = requireProof(env, "env");
        KeYEnvironment<DefaultUserInterfaceControl> env2 =
            KeYEnvironment.load(exampleDir.resolve(EXAMPLE_PROOF));
        Proof foreign = requireProof(env2, "env2");

        GUIProofTreeModel model = new GUIProofTreeModel(displayed);
        forceExpand((TreeNode) model.getRoot());

        // keep a node of the foreign proof (Node keeps its proof reference), then dispose it
        Node foreignRoot = foreign.root();
        foreign.dispose();

        assertThrows(IllegalStateException.class, () -> model.updateTree(foreignRoot),
            "walking a foreign disposed proof's node must fail fast");

        env.dispose();
        env2.dispose();
    }

    private static void forceExpand(TreeNode node) {
        int count = node.getChildCount();
        for (int i = 0; i < count; i++) {
            forceExpand(node.getChildAt(i));
        }
    }
}
