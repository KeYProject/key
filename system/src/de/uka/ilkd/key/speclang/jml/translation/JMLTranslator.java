// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;


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
                
    	final KeYJMLParser parser = new KeYJMLParser(expr,
    					       	     services,
    					       	     specInClass,
    					       	     selfVar,
    					       	     paramVars, 
    					       	     resultVar, 
    					       	     excVar,
    					       	     heapAtPre);
    	
    	final Term result = parser.parseExpression();    	
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
        
        final KeYJMLParser parser = new KeYJMLParser(signalsExpr,
                                               	     services,
                                               	     specInClass,
                                               	     selfVar,
                                               	     paramVars, 
                                               	     resultVar, 
                                               	     excVar,
                                               	     heapAtPre);
        final Term result = parser.parseSignals();
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

        final KeYJMLParser parser = new KeYJMLParser(signalsOnlyExpr,
                                               	     services,
                                               	     specInClass,
                                               	     null,
                                               	     null, 
                                               	     null, 
                                               	     excVar,
                                               	     null);
        
        final Term result = parser.parseSignalsOnly();
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
            
        final KeYJMLParser parser = new KeYJMLParser(assignableExpr,
                                               	     services,
                                               	     specInClass,
                                               	     selfVar,
                                               	     paramVars, 
                                               	     null, 
                                               	     null,
                                               	     null);
        
        final Term result = parser.parseAssignable();
        return result;
    }

    /**
     * Translates an expression as it occurs in JML assignable-clauses.
     */
    public ImmutableList<Term> translateSecureForExpression(
                                    	PositionedString assignableExpr,
                                        KeYJavaType specInClass,
                                        ProgramVariable selfVar,
                                        ImmutableList<ProgramVariable> paramVars)
            throws SLTranslationException {

        final KeYJMLParser parser = new KeYJMLParser(assignableExpr,
                                               	     services,
                                               	     specInClass,
                                               	     selfVar,
                                               	     paramVars,
                                               	     null,
                                               	     null,
                                               	     null);

        final ImmutableList<Term> result = parser.parseSecureFor();
        return result;
    }


    /**
     * Translates an expression as it occurs in JML assignable-clauses.
     */
    public ImmutableList<Term> translateDeclassifyExpression(
                                    	PositionedString assignableExpr,
                                        KeYJavaType specInClass,
                                        ProgramVariable selfVar,
                                        ImmutableList<ProgramVariable> paramVars)
            throws SLTranslationException {

        final KeYJMLParser parser = new KeYJMLParser(assignableExpr,
                                               	     services,
                                               	     specInClass,
                                               	     selfVar,
                                               	     paramVars,
                                               	     null,
                                               	     null,
                                               	     null);

        final ImmutableList<Term> result = parser.parseDeclassify();
        return result;
    }

    
    /**
     * Translates an expression as it occurs in JML represents-clauses.
     */
    public Pair<ObserverFunction,Term> translateRepresentsExpression(
                                    	PositionedString representsExpr,
                                        KeYJavaType specInClass,
                                        ProgramVariable selfVar)
            throws SLTranslationException {        
            
        final KeYJMLParser parser = new KeYJMLParser(representsExpr,
                                               	     services,
                                               	     specInClass,
                                               	     selfVar,
                                               	     null, 
                                               	     null, 
                                               	     null,
                                               	     null);
        
        final Pair<ObserverFunction,Term> result = parser.parseRepresents();
        return result;
    }    
    
    
   /**
     * Translates an expression as it occurs in our custom class-level accessible clauses.
     */
    public Triple<ObserverFunction,Term,Term> translateDependsExpression(
                                    	PositionedString accessibleExpr,
                                        KeYJavaType specInClass,
                                        ProgramVariable selfVar)
            throws SLTranslationException {        
            
        final KeYJMLParser parser = new KeYJMLParser(accessibleExpr,
                                               	     services,
                                               	     specInClass,
                                               	     selfVar,
                                               	     null, 
                                               	     null, 
                                               	     null,
                                               	     null);
        
        final Triple<ObserverFunction,Term,Term> result = parser.parseDepends();
        return result;
    }        
    
    
    public ImmutableList<ProgramVariable> translateVariableDeclaration(PositionedString variableDecl) 
            throws SLTranslationException {
        final KeYJMLParser parser = new KeYJMLParser(variableDecl,
                                               	     services,
                                               	     null,
                                               	     null,
                                               	     null,
                                               	     null, 
                                               	     null,
                                               	     null);
        
        final ImmutableList<ProgramVariable> result = parser.parseVariableDeclaration();
        return result;
    }
}
