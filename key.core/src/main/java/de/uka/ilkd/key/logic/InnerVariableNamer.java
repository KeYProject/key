/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;


/**
 * Implements "inner renaming", i.e. renaming - if a new variable entering the globals causes a name
 * clash - this "inner" variable, and leaving the clashing "outer" one untouched.
 */
public class InnerVariableNamer extends VariableNamer {

    public InnerVariableNamer(Services services) {
        super(services);
    }

    /**
     * returns the maximum counter for the passed basename in the passed globals and the passed
     * program
     */
    private int getMaxCounterInGlobalsAndProgram(String basename,
            Iterable<ProgramElementName> globals, ProgramElement program,
            PosInProgram posOfDeclaration) {
        int maxInGlobals = getMaxCounterInGlobals(basename, globals);
        int maxInProgram = getMaxCounterInProgram(basename, program, posOfDeclaration);

        return (Math.max(maxInGlobals, maxInProgram));
    }

    public ProgramVariable rename(ProgramVariable var, Goal goal, PosInOccurrence posOfFind) {
        ProgramElementName name = var.getProgramElementName();
        BasenameAndIndex bai = getBasenameAndIndex(name);
        Iterable<ProgramElementName> globals = wrapGlobals(goal.node().getLocalProgVars());
        map.clear();

        // prepare renaming of inner var
        final NameCreationInfo nci = MethodStackInfo.create(getProgramFromPIO(posOfFind));
        ProgramElementName newname = null;
        // ProgramElementName branchUniqueName = null;

        // Name proposal = services.getProof().getNameRecorder().getProposal();
        Name proposal = services.getNameRecorder().getProposal();

        if (proposal != null) {
            newname = new ProgramElementName(proposal.toString(), nci);
        }
        if (newname == null || !isUniqueInGlobals(newname.toString(), globals)
                || services.getNamespaces().lookupLogicSymbol(newname) != null) {
            newname = createName(bai.basename, bai.index, nci);
            int newcounter = getMaxCounterInGlobalsAndProgram(bai.basename, globals,
                getProgramFromPIO(posOfFind), null);
            final NamespaceSet namespaces = services.getNamespaces();

            while (!isUniqueInGlobals(newname.toString(), globals)
                    || namespaces.lookupLogicSymbol(newname) != null) {
                newcounter += 1;
                newname = createName(bai.basename, newcounter, nci);
            }
        }

        ProgramVariable newvar = var;
        if (!newname.equals(name)) {
            newvar = new LocationVariable(newname, var.getKeYJavaType());
            map.put(var, newvar);
            renamingHistory = map;
        }

        assert newvar != null;
        assert isUniqueInGlobals(newvar.name().toString(), globals);
        assert services.getNamespaces().lookupLogicSymbol(newvar.name()) == null;
        return newvar;
    }

}
