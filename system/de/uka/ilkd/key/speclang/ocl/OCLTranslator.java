// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.ocl;

import java.io.StringReader;
import java.util.Map;

import antlr.ANTLRException;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.EverythingLocationDescriptor;
import de.uka.ilkd.key.logic.ListOfInteger;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.SLListOfInteger;
import de.uka.ilkd.key.logic.SetAsListOfLocationDescriptor;
import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.IteratorOfParsableVariable;
import de.uka.ilkd.key.logic.op.ListOfParsableVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.parser.KeYLexer;
import de.uka.ilkd.key.parser.KeYParser;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.parser.ocl.AxiomCollector;
import de.uka.ilkd.key.parser.ocl.FunctionFactory;
import de.uka.ilkd.key.parser.ocl.KeYOclLexer;
import de.uka.ilkd.key.parser.ocl.KeYOclParser;
import de.uka.ilkd.key.parser.ocl.OCLTranslationError;
import de.uka.ilkd.key.speclang.FormulaWithAxioms;
import de.uka.ilkd.key.speclang.SLTranslationError;
import de.uka.ilkd.key.util.Debug;


/**
 * Translates OCL expressions to DL.
 */
public class OCLTranslator {
    private final Services services;
    private ListOfInteger parserCounters = SLListOfInteger.EMPTY_LIST;
    
    
    public OCLTranslator(Services services) {
	this.services = services;
    }
    
    
    private FormulaWithAxioms translatePrePostInv(
	    				String expr,
	    				ParsableVariable selfVar,
	    				ListOfParsableVariable paramVars,
	    				ParsableVariable resultVar,
	    				ParsableVariable excVar) throws SLTranslationError {
	AxiomCollector ac = new AxiomCollector();
	FunctionFactory.INSTANCE.resetFactory(services, ac);
	
	Term resultFormula = null;
	Map resultAxioms = null;
	
        try {
        	//create lexer and parser
	        StringReader stream = new StringReader(expr);
	        KeYOclLexer lexer   = new KeYOclLexer(stream);
	        KeYOclParser parser = new KeYOclParser(lexer,
	    	    				   services,
	        				       	   ac, 
	        				       	   selfVar, 
	        				       	   paramVars, 
	        				       	   resultVar, 
	        				       	   excVar);
	        
	        //initialise counters
	        parser.setCounters(parserCounters);
	
	        //parse the expression
	        if (expr.length() > 0) {
	            resultFormula = parser.parseExpression();
	        } else {
	            resultFormula = TermBuilder.DF.tt();
	        }
	    
	        //get created Axioms
	        resultAxioms = ac.getAxioms();
	        
	        //save counter values
	        parserCounters = parser.getCounters();
        } catch (ANTLRException e) {
        	if(e instanceof OCLTranslationError) {
        		throw ((OCLTranslationError)e).getSLTranslationError();
        	} else {
        		Debug.fail("OCLTranslator : " + e.getMessage());
        	}
        }
    	return new FormulaWithAxioms(resultFormula, resultAxioms);
    }
    
    
    public FormulaWithAxioms translatePre(String pre,
                                          ParsableVariable selfVar, 
                                          ListOfParsableVariable paramVars) throws SLTranslationError {
        return translatePrePostInv(pre, selfVar, paramVars, null, null);
    }

  
    public FormulaWithAxioms translatePost(String post,
                                           ParsableVariable selfVar, 
                                           ListOfParsableVariable paramVars, 
                                           ParsableVariable resultVar, 
                                           ParsableVariable exceptionVar) throws SLTranslationError {
        return translatePrePostInv(post, 
        			   selfVar, 
        			   paramVars, 
        			   resultVar, 
        			   exceptionVar);
    }

  
    public SetOfLocationDescriptor translateModifies(
                                          String modifies,
                                          ParsableVariable selfVar, 
                                          ListOfParsableVariable paramVars) throws SLTranslationError {
        if(modifies == null || modifies.equals("")) {
            return SetAsListOfLocationDescriptor.EMPTY_SET
                                                .add(EverythingLocationDescriptor.INSTANCE);
        }
        
        NamespaceSet nss = services.getNamespaces().copy();
        IteratorOfParsableVariable it = paramVars.prepend(selfVar).iterator();
        while(it.hasNext()) {
            ParsableVariable pv = it.next();
            if(pv instanceof LogicVariable) {
                nss.variables().add(pv);
            } else {
                assert pv instanceof ProgramVariable;
                nss.programVariables().add(pv);
            }
        }
        
        try {
            KeYParser parser = new KeYParser(ParserMode.TERM, 
                                             new KeYLexer(new StringReader(modifies),
                                                          null),
                                             "", 
                                             TermFactory.DEFAULT, 
                                             services,
                                             nss);
            return parser.location_list();
        } catch(Exception e) {
            throw new SLTranslationError(e.getMessage(), 0, 0);
        }
    }

  
    public FormulaWithAxioms translateInv(String inv, 
	    				  ParsableVariable selfVar) throws SLTranslationError {
        return translatePrePostInv(inv, selfVar, null, null, null);
    }
}
