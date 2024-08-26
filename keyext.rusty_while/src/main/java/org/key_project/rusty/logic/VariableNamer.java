/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import org.key_project.rusty.Services;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.proof.InstantiationProposer;
import org.key_project.rusty.rule.TacletApp;
import org.key_project.util.collection.ImmutableList;


/**
 * Responsible for program variable naming issues.
 */
public abstract class VariableNamer implements InstantiationProposer {
    /**
     * default basename for variable name proposals
     */
    private static final String DEFAULT_BASENAME = "var";

    /**
     * status of suggestive name proposing
     */
    private static boolean suggestiveOff = true;

    /**
     * pointer to services object
     */
    protected final Services services;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    /**
     * @param services pointer to services object
     */
    public VariableNamer(Services services) {
        this.services = services;
    }

    // precondition: sv.sort()==ProgramSVSort.VARIABLE
    public String getSuggestiveNameProposalForProgramVariable(SchemaVariable sv, TacletApp app,
            Services services, ImmutableList<String> previousProposals) {
        if (suggestiveOff) {
            return getProposal(app, sv, services, null, previousProposals);
        }

        String proposal = "TODO";
        try {
            // TODO
        } catch (Exception e) {
            return getProposal(app, sv, services, null, previousProposals);
        }
        return proposal;
    }
}
