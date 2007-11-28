// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.op.ArrayOfLocation;
import de.uka.ilkd.key.logic.op.NRFunctionWithExplicitDependencies;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.encapsulation.UniverseAnalyser;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;


public class Universes extends AbstractMetaOperator {
    public Sort sort(Term[] term) {
        return Sort.FORMULA;
    }
    
    
    public Universes() {
        super(new Name("#Universes"), 1);
    }


    public Term calculate(Term term, 
                          SVInstantiations svInst, 
                          Services services) {
        Term programTerm = term.sub(0);
        ProgramElement pi = programTerm.javaBlock().program();
        Term phiTerm = programTerm.sub(0);
        
        //get field sets
        NRFunctionWithExplicitDependencies phiOp 
                = (NRFunctionWithExplicitDependencies) phiTerm.op();
        Debug.assertTrue(phiOp.getNumPartitions() == 3);
        ArrayOfLocation R = phiOp.getDependencies(0);
        ArrayOfLocation P = phiOp.getDependencies(1);
        ArrayOfLocation F = phiOp.getDependencies(2);
        Debug.assertTrue(R != null && P != null && F != null);
                
        //perform analysis
        UniverseAnalyser ua = new UniverseAnalyser();
        if(ua.analyse(R, P, F, pi, svInst, services)) {
            return TermFactory.DEFAULT.createJunctorTerm(Op.TRUE);
        } else {
            return programTerm;
        }
    }
}
