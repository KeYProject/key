/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof;

import org.key_project.rusty.Services;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.rule.TacletApp;
import org.key_project.util.collection.ImmutableList;

/**
 * Provides proposals for schema variable instantiations.
 */
public interface InstantiationProposer {

    /**
     * Returns an instantiation proposal for the schema variable var.
     *
     * @param app the taclet app
     * @param var the schema variable to be instantiated
     * @param services pointer to services object
     * @param undoAnchor node to be used as undo anchor
     * @param previousProposals a list of other proposals which should be taken into account (e.g.
     *        for name uniqueness), or null
     */
    String getProposal(TacletApp app, SchemaVariable var, Services services, Node undoAnchor,
            ImmutableList<String> previousProposals);
}
