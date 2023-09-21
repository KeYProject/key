/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;


/**
 * Composite of instantiation proposers.
 */
public class InstantiationProposerCollection implements InstantiationProposer {

    private ImmutableList<InstantiationProposer> proposers =
        ImmutableSLList.nil();

    /**
     * adds an instantiation proposer to the collection
     */
    public void add(InstantiationProposer proposer) {
        proposers = proposers.append(proposer);
    }


    public String getProposal(TacletApp app, SchemaVariable var, Services services, Node undoAnchor,
            ImmutableList<String> previousProposals) {
        for (InstantiationProposer proposer1 : proposers) {
            InstantiationProposer proposer = proposer1;
            String proposal =
                proposer.getProposal(app, var, services, undoAnchor, previousProposals);
            if (proposal != null) {
                return proposal;
            }
        }

        return null;
    }
}
