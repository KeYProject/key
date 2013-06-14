// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;


/**
 * Implements "inner renaming", i.e. renaming - if a new variable entering the
 * globals causes a name clash - this "inner" variable, and leaving the clashing
 * "outer" one untouched.
 */
public class InnerVariableNamer extends VariableNamer {

    public InnerVariableNamer(Services services) {
    	super(services);
    }

    /**
     * returns the maximum counter for the passed basename in the passed globals
     * and the passed program
     */
    private int getMaxCounterInGlobalsAndProgram(String basename,
    				 		 Globals globals,
						 ProgramElement program,
						 PosInProgram posOfDeclaration) {
	int maxInGlobals = getMaxCounterInGlobals(basename, globals);
	int maxInProgram = getMaxCounterInProgram(basename,
						  program,
						  posOfDeclaration);

	return (maxInGlobals > maxInProgram ? maxInGlobals : maxInProgram);
    }

    public ProgramVariable rename(ProgramVariable var,
                                  Goal goal,
                                  PosInOccurrence posOfFind) {
	ProgramElementName name = var.getProgramElementName();
	BasenameAndIndex bai = getBasenameAndIndex(name);
	Globals globals = wrapGlobals(goal.getGlobalProgVars());
	map.clear();

	//prepare renaming of inner var
	final NameCreationInfo nci = getMethodStack(posOfFind);
	ProgramElementName newname = null;

	// Name proposal = services.getProof().getNameRecorder().getProposal();
        Name proposal = services.getNameRecorder().getProposal();

	if (proposal != null) {
	    newname = new ProgramElementName(proposal.toString(), nci);
	}
	if (newname == null || !isUniqueInGlobals(newname.toString(), globals)
	        || services.getNamespaces()
	        .lookupLogicSymbol(newname)!=null) {
	    newname = createName(bai.basename, bai.index, nci);
            int newcounter = getMaxCounterInGlobalsAndProgram(
                            bai.basename,
                            globals,
                            getProgramFromPIO(posOfFind),
                            null);
            final NamespaceSet namespaces = services.getNamespaces();
            while (!isUniqueInGlobals(newname.toString(), globals) ||
                    namespaces.lookupLogicSymbol(newname)!=null) {
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
        assert services.getNamespaces().lookupLogicSymbol(newvar.name())==null;
        return newvar;
    }

}
