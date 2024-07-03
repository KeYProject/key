/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package org.key_project.ui.interactionlog.model;

import java.util.Optional;
import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlRootElement;

import de.uka.ilkd.key.gui.WindowUserInterfaceControl;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;

@XmlRootElement()
@XmlAccessorType(XmlAccessType.FIELD)
public class PruneInteraction extends NodeInteraction {
    private static final long serialVersionUID = -8499747129362589793L;

    public PruneInteraction() {
    }

    public PruneInteraction(Node node) {
        super(node);
    }

    @Override
    public String toString() {
        return "prune";
    }

    @Override
    public String getMarkdown() {
        return String.format("## Prune%n%n"
            + "**Date**: %s%n"
            + "prune to node %s%n", getCreated(), getNodeId());
    }

    @Override
    public String getProofScriptRepresentation() {
        return String.format("prune %s%n", getNodeId());
    }

    @Override
    public void reapply(WindowUserInterfaceControl uic, Goal goal) throws Exception {
        Optional<Node> node = getNodeId().findNode(goal.proof());
        node.ifPresent(node1 -> goal.proof().pruneProof(node1));
    }
}
