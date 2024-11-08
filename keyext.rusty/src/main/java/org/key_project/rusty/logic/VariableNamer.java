/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import java.util.HashMap;
import java.util.LinkedHashMap;

import org.key_project.rusty.Services;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.proof.Goal;
import org.key_project.rusty.proof.InstantiationProposer;
import org.key_project.rusty.proof.Node;
import org.key_project.rusty.rule.NewVarcond;
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
    protected HashMap<ProgramVariable, ProgramVariable> renamingHistory =
        new LinkedHashMap<>();

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    /**
     * @param services pointer to services object
     */
    public VariableNamer(Services services) {
        this.services = services;
    }

    /**
     * proposes a unique name for the instantiation of a schema variable
     * <p>
     * <strong>Warning:</strong> The current version does not yet guarantee a unique name,
     * but it is very important that this is implemented in the future.
     *
     * @param app the taclet app
     * @param var the schema variable to be instantiated
     * @param services not used
     * @param undoAnchor not used
     * @param previousProposals list of names which should be considered taken, or null
     * @return the name proposal, or null if no proposal is available
     */
    public String getProposal(TacletApp app, SchemaVariable var, Services services, Node undoAnchor,
            ImmutableList<String> previousProposals) {
        // TODO change this to be the real version of VariableNamer in key.core
        // Currently, a very basic approach is taken that uses the first letter of the type
        // similar to what is done in VariableNamer#getBaseNameProposal(Type type) in key.core
        NewVarcond nv = app.taclet().varDeclaredNew(var);
        String name = nv.getType().name().toString();
        String result;
        if (!name.isEmpty()) {
            result = name.substring(0, 1).toLowerCase();
        } else {
            result = "x"; // use default name otherwise
        }
        return result;
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

    /**
     * intended to be called when symbolically executing a variable declaration; resolves any naming
     * conflicts between the new variable and other global variables by renaming the new variable
     * and / or other variables
     *
     * @param var the new program variable
     * @param goal the goal
     * @param posOfFind the PosInOccurrence of the currently executed program
     * @return the renamed version of the var parameter
     */
    public abstract ProgramVariable rename(ProgramVariable var, Goal goal,
            PosInOccurrence posOfFind);

    public HashMap<ProgramVariable, ProgramVariable> getRenamingMap() {
        return renamingHistory;
    }
}
