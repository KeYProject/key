/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io.intermediate;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.rule.merge.CloseAfterMerge;
import de.uka.ilkd.key.util.Pair;

import org.key_project.util.collection.ImmutableList;

/**
 * Encapsulates intermediate information for constructing a close-join-partner rule application.
 *
 * @author Dominic Scheurer
 */
public class MergePartnerAppIntermediate extends BuiltInAppIntermediate {

    private int mergeNodeId = 0;

    /**
     * Constructs a new close-merge-partner intermediate application.
     *
     * @param ruleName The name of the rule; should be "MergeAfterJoin".
     * @param pos Position information for the merge rule application (Symbolic State - Program
     *        Counter formula).
     * @param mergeNodeId The ID of the corresponding merge node.
     * @param newNames New names registered in the course of partner goal closing.
     */
    public MergePartnerAppIntermediate(String ruleName, Pair<Integer, PosInTerm> pos,
            int mergeNodeId, ImmutableList<Name> newNames) {
        super(ruleName, pos, null, null, null, newNames);

        assert ruleName.equals(CloseAfterMerge.INSTANCE.name().toString())
                : "Check if something should be changed when implementing a new rule for merge partners.";

        this.mergeNodeId = mergeNodeId;
    }

    /**
     * @return The ID of the corresponding merge node.
     */
    public int getMergeNodeId() {
        return mergeNodeId;
    }

}
