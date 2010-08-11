// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.encapsulation;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.Location;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public class UniverseAnalyser {

    public static boolean showDialog = false;

    private void verbose(Object o) {
        System.out.println(o);
    }
    
    
    private void printStartup(ImmutableArray<Location> R, 
                              ImmutableArray<Location> P, 
                              ImmutableArray<Location> F,
                              ProgramElement pi) {
        verbose("Universe analysis running with parameters...");
        verbose("R  = " + R);
        verbose("P  = " + P);
        verbose("F  = " + F);
        verbose("pi = " + pi);
    }


    private void printCoveredMethods(ImmutableList<ProgramMethod> coveredMethods) {
        verbose("The following method bodies have been analysed:");
        Iterator<ProgramMethod> it = coveredMethods.iterator();
        int i = 1;
        while(it.hasNext()) {
            verbose("(" + i++ + ") " + it.next());
        }
    }

    
    private void printConstraints(ImmutableList<TypeSchemeConstraint> constraints,
                                  TypeSchemeConstraint andConstraint) {
        verbose("The following constraints have been generated:");
        Iterator<TypeSchemeConstraint> it = constraints.iterator();
        int i = 1;
        while(it.hasNext()) {
            verbose("(" + i++ + ") " + it.next());
        }
        
        verbose("The value ranges of the variables are:");
        Iterator<TypeSchemeVariable> it2 
                        = andConstraint.getFreeVars().iterator();
        i = 1;
        while(it2.hasNext()) {
            TypeSchemeVariable var = it2.next();
            verbose("(" + i++ + ") " + var + ": " + var.getDefaultValue());
        }
    }
    
    
    private void printSolution(boolean success, TypeSchemeConstraint andConstraint) {
        if(success) {
            verbose("A solution has been found:");
            
            Iterator<TypeSchemeVariable> it = andConstraint.getFreeVars().iterator();
            int i = 1;
            while(it.hasNext()) {
                TypeSchemeVariable var = it.next();
                verbose("(" + i++ + ") " + var + ": " + var.evaluate());
            }
        } else {
            verbose("No solution could be found.");
        }
    }
       
    
    public boolean analyse(ImmutableArray<Location> R,
		           ImmutableArray<Location> P, 
		           ImmutableArray<Location> F,
		           ProgramElement pi, 
                           SVInstantiations svInst, 
                           Services services) {                 
        //give debug output
        printStartup(R, P, F, pi);

        //check if pi contains any predefined local reference variables 
        //(not allowed)
        FreeProgramVariableDetector fpvd 
            = new FreeProgramVariableDetector(pi, services);
        if(fpvd.findFreePV()) {
            verbose("There is a predefined local reference variable in pi. "
                    + "Canceling.");
            return false;
        }
        
        //create map for annotations
        Map /*Location -> TypeSchemeTerm*/ annotations
                        = new HashMap();
                    
        //annotate fields
	for(int i = 0; i < R.size(); i++) {
	    annotations.put(R.get(i), TypeSchemeUnion.REP);
	}

        for(int i = 0; i < P.size(); i++) {
            annotations.put(P.get(i), TypeSchemeUnion.PEER);
        }

        for(int i = 0; i < F.size(); i++) {
            annotations.put(F.get(i), TypeSchemeUnion.READONLY);
        }
        
        //extract constraints
        verbose("Generating constraints...");
        TypeSchemeConstraintExtractor extractor
                        = new TypeSchemeConstraintExtractor(services);
        ImmutableList<TypeSchemeConstraint> constraints = extractor.extract(pi, 
                                                                   annotations, 
                                                                   svInst);
        TypeSchemeConstraint andConstraint
                        = new TypeSchemeAndConstraint(constraints);

        //give debug output
        printCoveredMethods(extractor.getCoveredMethods());
        printConstraints(constraints, andConstraint);
        
        //try to solve the constraints
        verbose("Trying to find a solution...");
        TypeSchemeConstraintSolver solver = new TypeSchemeConstraintSolver();
        boolean success = solver.solve(andConstraint);

        //give debug output
        printSolution(success, andConstraint);

        //show dialog
        if(!success && constraints.size() > 1 && showDialog) {
            new UniverseDialog(constraints);
        }
        
        //return result
        verbose("Finished.");
        return success;
    }
}
