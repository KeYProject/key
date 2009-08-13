// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.jml.translation;

import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.speclang.FormulaWithAxioms;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;


/**
 * Translates JML expressions to FOL.
 */
class JMLTranslator {
    
    private final Services services;
    
    
    public JMLTranslator(Services services) {
	this.services = services;
    }
    
    
    /**
     * Translates a normal top-level JML expression, i.e. a formula.
     */
    public FormulaWithAxioms translateExpression(
	    				PositionedString expr,
                                        KeYJavaType specInClass,
                                        ProgramVariable selfVar, 
                                        ListOfProgramVariable paramVars,
                                        ProgramVariable resultVar,
                                        ProgramVariable excVar,
                                        Term heapAtPre) 
            throws SLTranslationException {
        assert expr != null;
        assert specInClass != null;
                
    	KeYJMLParser parser = new KeYJMLParser(expr,
    					       services,
                                               specInClass,
    					       selfVar,
    					       paramVars, 
    					       resultVar, 
    					       excVar,
                                               heapAtPre);
    	
    	FormulaWithAxioms result = null;
    	
//    	System.out.println("JMLTranslator.translateExpression("+expr+")" + " in " + expr.fileName);
    	
    	result = parser.parseExpression();
    	
//    	System.out.println(result.getFormula().toString());
//    	System.out.println();
    	
    	return result;
    }

    
    /**
     * Translates an expression as it occurs in JML signals-clauses, 
     * i.e. something of the form
     *       "(typename) expression"
     * or
     *       "(typename varname) expression"
     */
    public FormulaWithAxioms translateSignalsExpression(
	    				PositionedString signalsExpr,
                                        KeYJavaType specInClass,
                                        ProgramVariable selfVar, 
                                        ListOfProgramVariable paramVars, 
                                        ProgramVariable resultVar, 
                                        ProgramVariable excVar,
                                        Term heapAtPre)
            throws SLTranslationException {
        
        KeYJMLParser parser = new KeYJMLParser(signalsExpr,
                                               services,
                                               specInClass,
                                               selfVar,
                                               paramVars, 
                                               resultVar, 
                                               excVar,
                                               heapAtPre);
        
        FormulaWithAxioms result = null;
        
//      System.out.println("JMLTranslator.translateSignalsExpression("+signalsExpr+") results: ");

        result = parser.parseSignals();
        
//      System.out.println(result.getFormula().toString());
//      System.out.println();
        
        return result;
    }
    
    
    /**
     * Translates an expression as it occurs in JML signals_only-clauses,
     * i.e. a list of types.
     */
    public FormulaWithAxioms translateSignalsOnlyExpression(
	    				PositionedString signalsOnlyExpr,
                                        KeYJavaType specInClass,
	    				ProgramVariable excVar)
            throws SLTranslationException {

        KeYJMLParser parser = new KeYJMLParser(signalsOnlyExpr,
                                               services,
                                               specInClass,
                                               null,
                                               null, 
                                               null, 
                                               excVar,
                                               null);
        
        FormulaWithAxioms result = null;
        
//          System.out.println("JMLTranslator.translateSignalsOnlyExpression("+signalsOnlyExpr+") results: ");

            result = parser.parseSignalsOnly();
        
//          System.out.println(result.getFormula().toString());
//          System.out.println();
        
        return result;
    }

  
    /**
     * Translates an expression as it occurs in JML assignable-clauses.
     */
    public Term translateAssignableExpression(
                                    	PositionedString assignableExpr,
                                        KeYJavaType specInClass,
                                        ProgramVariable selfVar, 
                                        ListOfProgramVariable paramVars)
            throws SLTranslationException {        
            
        KeYJMLParser parser = new KeYJMLParser(assignableExpr,
                                               services,
                                               specInClass,
                                               selfVar,
                                               paramVars, 
                                               null, 
                                               null,
                                               null);
        
//      System.out.println("JMLTranslator.translateAssignableExpression("+assignableExpr+") results: ");

        Term result = parser.parseAssignable();
        
//      System.out.println(result);
//      System.out.println();
        
        return result;
    }
    
    
    public ListOfProgramVariable translateVariableDeclaration(PositionedString variableDecl) 
            throws SLTranslationException {
        KeYJMLParser parser = new KeYJMLParser(variableDecl,
                                               services,
                                               null,
                                               null,
                                               null,
                                               null, 
                                               null,
                                               null);
        
        ListOfProgramVariable result = parser.parseVariableDeclaration();
        
//      System.out.println(result);
//      System.out.println();
        
        return result;
    }
}
