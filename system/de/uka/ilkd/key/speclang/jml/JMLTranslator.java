//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.jml;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
import de.uka.ilkd.key.logic.op.ListOfParsableVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.speclang.FormulaWithAxioms;


/**
 * Translates JML expressions to DL.
 */
public class JMLTranslator {
    private final Services services;
    
    
    public JMLTranslator(Services services) {
	this.services = services;
    }
    
    
    public FormulaWithAxioms translateRequires(String requires,
                                               ParsableVariable selfVar, 
                                               ListOfParsableVariable paramVars) {
        return null;//TODO
    }
  

    public FormulaWithAxioms translateEnsures(String ensures,
                                              ParsableVariable selfVar, 
                                              ListOfParsableVariable paramVars, 
                                              ParsableVariable resultVar, 
                                              ParsableVariable excVar) {
        return null;//TODO
    }

  
    public FormulaWithAxioms translateSignals(String signals,
                                              ParsableVariable selfVar, 
                                              ListOfParsableVariable paramVars, 
                                              ParsableVariable resultVar, 
                                              ParsableVariable excVar) {
        return null;//TODO
    }

  
    public FormulaWithAxioms translateDiverges(String diverges,
                                               ParsableVariable selfVar, 
                                               ListOfParsableVariable paramVars) {
        return null;//TODO
    }

  
    public SetOfLocationDescriptor translateAssignable(
                                               String modifies,
                                               ParsableVariable selfVar, 
                                               ListOfParsableVariable paramVars) {
        return null;//TODO
    }

  
    public FormulaWithAxioms translateInv(String inv, ParsableVariable selfVar) {
        return null;//TODO
    }
}
