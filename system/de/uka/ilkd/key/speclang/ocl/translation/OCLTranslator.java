//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.ocl.translation;

import java.io.StringReader;
import java.util.Map;

import antlr.RecognitionException;
import antlr.TokenStreamException;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ListOfInteger;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.SLListOfInteger;
import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.IteratorOfParsableVariable;
import de.uka.ilkd.key.logic.op.ListOfParsableVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.parser.KeYLexer;
import de.uka.ilkd.key.parser.KeYParser;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.speclang.FormulaWithAxioms;
import de.uka.ilkd.key.speclang.translation.AxiomCollector;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;


/**
 * Translates OCL expressions to FOL.
 */
class OCLTranslator {
    private final Services services;
    private ListOfInteger parserCounters = SLListOfInteger.EMPTY_LIST;
    
    
    public OCLTranslator(Services services) {
	this.services = services;
    }
    
    
    /**
     * Translates a normal top-level OCL expression, i.e. a formula.
     */
    public FormulaWithAxioms translateExpression(
	    				String expr,
                                        KeYJavaType specInClass,
	    				ParsableVariable selfVar,
	    				ListOfParsableVariable paramVars,
	    				ParsableVariable resultVar,
	    				ParsableVariable excVar,
                                        Map /*Operator (normal) 
                                           -> Function (atPre)*/ atPreFunctions) 
    		throws SLTranslationException {
	assert expr != null && !expr.equals("");
	assert specInClass != null;
	AxiomCollector ac = new AxiomCollector();
	FunctionFactory.INSTANCE.resetFactory(services, ac);
	
	Term resultFormula = null;
	Map resultAxioms = null;
	
        //create lexer and parser
        StringReader stream = new StringReader(expr);
        KeYOCLLexer lexer   = new KeYOCLLexer(stream);
        KeYOCLParser parser = new KeYOCLParser(lexer,
                                               Position.UNDEFINED, //TODO
    	    				       services,
                                               specInClass,
        				       ac, 
        				       selfVar, 
        				       paramVars, 
        				       resultVar, 
        				       excVar,
                                               atPreFunctions);
        
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

    	return new FormulaWithAxioms(resultFormula, resultAxioms);
    }

  
    /**
     * Translates an expression as it occurs in KeY-OCL modifies expressions.
     */
    public SetOfLocationDescriptor translateModifiesExpression(
                                          String modifiesExpr,
                                          ParsableVariable selfVar, 
                                          ListOfParsableVariable paramVars)
		throws SLTranslationException {
	assert modifiesExpr != null && !modifiesExpr.equals("");
		
	//add self and parameter variables to namespace
	Namespace originalProgVars 
		= services.getNamespaces().programVariables();
	Namespace extendedProgVars
		= originalProgVars.copy();
	extendedProgVars.add(selfVar);
	IteratorOfParsableVariable it = paramVars.iterator();
	while(it.hasNext()) {
	    extendedProgVars.add(it.next());
	}
	services.getNamespaces().setProgramVariables(extendedProgVars);
	
	//create parser
        KeYParser parser 
        	= new KeYParser(ParserMode.TERM,
                                new KeYLexer(new StringReader(modifiesExpr), 
                                	     null),
                                "modifier string",
                                TermFactory.DEFAULT,
                                services,
                                services.getNamespaces());
        
        //parse
        try {
            return parser.location_list();
        } catch(RecognitionException e) {
            throw new SLTranslationException(e.getMessage(), 
                                         "no file",
        	    			 e.getLine(), 
        	    			 e.getColumn());
        } catch(TokenStreamException e) {
            throw new SLTranslationException(e.getMessage(),"no file", -1, -1);
        } finally {
            //set back namespace
            services.getNamespaces().setProgramVariables(originalProgVars);
        }
    }
}
