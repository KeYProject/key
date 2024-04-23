/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;

public class SearchInDatabaseAction extends KeyAction {
    private final CachingExtension extension;
    private final Node node;

    public SearchInDatabaseAction(CachingExtension extension, Node node) {
        this.extension = extension;
        this.node = node;

        setName("Search for hits in external database");
        setMenuPath("Proof Caching");
        setEnabled(node.proof().getOpenGoal(node) != null);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        var seq = node.sequent();
        var matches =
            extension.getDatabase().findMatching(node.proof().getSettings().getChoiceSettings(),
                seq, node.proof().getServices());
        if (!matches.isEmpty()) {
            node.register(matches.stream().findFirst().get(), CachedProofBranch.class);
            Goal openGoal = node.proof().getOpenGoal(node);
            node.proof().closeGoal(openGoal);
            extension.updateGUIState();
        }
    }
}
