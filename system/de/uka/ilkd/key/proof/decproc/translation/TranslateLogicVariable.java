// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.proof.decproc.translation;

import java.util.HashMap;
import org.apache.log4j.Logger;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.decproc.SmtAufliaTranslation;
import de.uka.ilkd.key.proof.decproc.smtlib.Signature;
import de.uka.ilkd.key.proof.decproc.smtlib.TermVariable;

/** This class represents the translation rule for <tt>LogicVariable</tt>s.
 * <p>
 * A <tt>LogicVariable</tt> is translated into a <tt>TermVariable</tt>, if it is of <tt>Sort</tt> INT or 
 * OBJECT. 
 * <p>
 * The name of this <tt>TermVariable</tt> is created out of the variable name and an id unique to
 * the <tt>LogicVariable</tt>. It further consists of a prefix indicating that it is a 
 * translation of a <tt>LogicVariable</tt> and a suffix that indicating the <tt>Sort</tt> of 
 * the translated <tt>LogicVariable</tt>
 *  
 * @author akuwertz
 * @version 1.0,  10/04/2006
 * 
 */
public class TranslateLogicVariable implements IOperatorTranslation {

    /* Additional fields */
    
    /** A cache for already translated <tt>LogicVariable</tt> instances */
    private final HashMap translatedLogicVars = new HashMap();
    
    /** A prefix used in the names of the created <tt>TermVariables</tt> to
     * indicate that they represent a translations of an <tt>LogicVariable</tt> */
    private static final String logicVarPrefix = "LogVar_";
    
    /** A suffix used in the name of the created <tt>TermVariables</tt> to indicate that it 
     * represents the translation of an integer <tt>ProgramVariable</tt> */
    private static final String logicVarIntSuffix = "_int";
    /** A suffix used in the name of the created <tt>TermVariables</tt> to indicate that it 
     * represents the translation of an object <tt>LogicVariable</tt> */
    private static final String logicVarObjectSuffix = "_object";
        
    /** A <tt>Logger</tt> for logging and debugging operator translation */
    private static final Logger logger = Logger.getLogger( TranslateLogicVariable.class.getName() );
        // Logger is created hierarchical to inherit configuration and behaviour from parent
    
    /* String constants for error messages */
    private static final String unsupportedLogicVar = "Translation of logic variable failed: ";
    private static final String unsupportedLogicVarFailure = "\nCaused by unsupported Sort: ";
    
    
    
    /* Public method implementation */
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.translation.IOperatorTranslation#isApplicable(de.uka.ilkd.key.logic.op.Operator)
     */
    public boolean isApplicable(Operator op) {
        return op instanceof LogicVariable;
    }

    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.translation.IOperatorTranslation#translate(de.uka.ilkd.key.logic.op.Operator, de.uka.ilkd.key.proof.decproc.translation.TermTranslationVisitor)
     */
    public Object translate(Operator op, TermTranslationVisitor ttVisitor) {
        
        Sort integerSort = ttVisitor.getServices().getTypeConverter().getIntegerLDT().targetSort();
        Sort currentSort = ((LogicVariable) op).sort();
        String generatedName;
        
        // If the logic variable has already been translated, return cached translation
        if ( translatedLogicVars.containsKey( op ) ) {
            logger.info( "Found a previously translated logic variable: " + op.name() );
            logger.info( "Returning cached translation for this logic variable" );
            return translatedLogicVars.get( op );
        }
        
        if ( currentSort.extendsTrans( integerSort )  ||  currentSort instanceof ObjectSort ) {    
            logger.info( "Found logic variable: " + op.name() );
            // Add a unique ID to the name of the term variable
            generatedName = logicVarPrefix +
                            SmtAufliaTranslation.legaliseIdentifier( op.name().toString() ) +
                            "_" + translatedLogicVars.size();
            Object translation;
            if ( currentSort.extendsTrans( integerSort ) ) {                
                generatedName += logicVarIntSuffix;
                logger.info( "Found integer sort for this logic variable, creating " +
                             "term variable and caching it" );
            } else {
                generatedName += logicVarObjectSuffix;
                logger.info( "Found object sort for this logic variable, creating " +
                             "term variable and caching it" );
            }
            logger.debug( "Term variable was given the name: " + generatedName );
            translation = new TermVariable( generatedName, Signature.constSignature( false ) );
            translatedLogicVars.put( op , translation );
            
            return translation;
        }
        
        // The given logic variable is of an untranslatable sort!
        logger.info( "Found unsupported logic variable, exiting with exception!" );
        throw new UnsupportedOperationException( unsupportedLogicVar + op.name() + 
                                                 unsupportedLogicVarFailure + currentSort );
    }

}
