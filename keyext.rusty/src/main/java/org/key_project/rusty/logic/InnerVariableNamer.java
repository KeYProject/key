/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import org.key_project.logic.Name;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.proof.Goal;
import org.key_project.rusty.proof.Node;
import org.key_project.rusty.rule.TacletApp;
import org.key_project.util.collection.ImmutableList;

public class InnerVariableNamer extends VariableNamer {
    public InnerVariableNamer(Services services) {
        super(services);
    }

    @Override
    public ProgramVariable rename(ProgramVariable var, Goal goal, PosInOccurrence posOfFind) {
        var name = var.name();
        BasenameAndIndex bai = getBasenameAndIndex(name);
        Iterable<Name> globals = wrapGlobals(goal.getNode().getLocalProgVars());
        map.clear();

        Name newName = new Name(bai.basename() + (bai.index() == 0 ? "" : "_" + bai.index()));
        int newcounter = getMaxCounterInGlobalsAndProgram(bai.basename(), globals,
            getProgramFromPIO(posOfFind), null);
        final NamespaceSet namespaces = services.getNamespaces();

        while (!isUniqueInGlobals(newName.toString(), globals)
                || namespaces.lookupLogicSymbol(newName) != null) {
            newcounter += 1;
            newName = new Name(bai.basename() + "_" + newcounter);
        }

        ProgramVariable newVar = var;
        if (!newName.equals(name)) {
            newVar = new ProgramVariable(newName, var.getKeYRustyType());
            map.put(var, newVar);
            renamingHistory = map;
        }

        assert isUniqueInGlobals(newVar.name().toString(), globals);
        assert services.getNamespaces().lookupLogicSymbol(newVar.name()) == null;
        return newVar;
    }

    /**
     * returns the maximum counter for the passed basename in the passed globals and the passed
     * program
     */
    private int getMaxCounterInGlobalsAndProgram(String basename,
            Iterable<Name> globals, RustyProgramElement program,
            PosInProgram posOfDeclaration) {
        int maxInGlobals = getMaxCounterInGlobals(basename, globals);
        int maxInProgram = getMaxCounterInProgram(basename, program, posOfDeclaration);

        return (Math.max(maxInGlobals, maxInProgram));
    }


    @Override
    public String getProposal(TacletApp app, SchemaVariable var, Services services, Node undoAnchor,
            ImmutableList<String> previousProposals) {
        return super.getProposal(app, var, services, undoAnchor, previousProposals);
        // return "";
    }
}
