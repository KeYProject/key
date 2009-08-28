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

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.Pair;


/**
 * Translates JML expressions to FOL.
 */
final class JMLTranslator {
    
    private final Services services;
    
    
    public JMLTranslator(Services services) {
	this.services = services;
    }
    
    
    /**
     * Translates a normal top-level JML expression, i.e. a formula.
     */
    public Term translateExpression(PositionedString expr,
                                    KeYJavaType specInClass,
                                    ProgramVariable selfVar, 
                                    ImmutableList<ProgramVariable> paramVars,
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
    	
    	Term result = null;
    	
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
    public Term translateSignalsExpression(
	    			PositionedString signalsExpr,
                                KeYJavaType specInClass,
                                ProgramVariable selfVar, 
                                ImmutableList<ProgramVariable> paramVars, 
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
        
        Term result = null;
        
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
    public Term translateSignalsOnlyExpression(
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
        
        Term result = null;
        
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
                                        ImmutableList<ProgramVariable> paramVars)
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
    
    
    /**
     * Translates an expression as it occurs in JML represents-clauses.
     */
    public Term translateRepresentsExpression(
                                    	PositionedString representsExpr,
                                        KeYJavaType specInClass,
                                        ProgramVariable selfVar)
            throws SLTranslationException {        
            
        KeYJMLParser parser = new KeYJMLParser(representsExpr,
                                               services,
                                               specInClass,
                                               selfVar,
                                               null, 
                                               null, 
                                               null,
                                               null);
        
//      System.out.println("JMLTranslator.translateRepresentsExpression("+representsExpr+") results: ");

        Term result = parser.parseRepresents();
        
//      System.out.println(result);
//      System.out.println();
        
        return result;
    }    
    
    
   /**
     * Translates an expression as it occurs in our custom class-level accessible clauses.
     */
    public Pair<Operator,Term> translateAccessibleExpression(
                                    	PositionedString representsExpr,
                                        KeYJavaType specInClass,
                                        ProgramVariable selfVar)
            throws SLTranslationException {        
            
        KeYJMLParser parser = new KeYJMLParser(representsExpr,
                                               services,
                                               specInClass,
                                               selfVar,
                                               null, 
                                               null, 
                                               null,
                                               null);
        
//      System.out.println("JMLTranslator.translateAccessibleExpression("+representsExpr+") results: ");

        Pair<Operator,Term> result = parser.parseAccessible();
        
//      System.out.println(result);
//      System.out.println();
        
        return result;
    }        
    
    
    public ImmutableList<ProgramVariable> translateVariableDeclaration(PositionedString variableDecl) 
            throws SLTranslationException {
        KeYJMLParser parser = new KeYJMLParser(variableDecl,
                                               services,
                                               null,
                                               null,
                                               null,
                                               null, 
                                               null,
                                               null);
        
        ImmutableList<ProgramVariable> result = parser.parseVariableDeclaration();
        
//      System.out.println(result);
//      System.out.println();
        
        return result;
    }
}
