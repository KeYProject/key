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
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.decproc.SmtAufliaTranslation;
import de.uka.ilkd.key.proof.decproc.smtlib.Signature;
import de.uka.ilkd.key.proof.decproc.smtlib.UninterpretedFuncTerm;
import de.uka.ilkd.key.proof.decproc.smtlib.UninterpretedPredFormula;


/** This class represents the translation rule for <tt>ProgramVariable</tt>s.
 * <p>
 * A <tt>ProgramVariable</tt> is translated into a constant. If it is of <tt>Sort</tt> INT or 
 * OBJECT, it will be translated into an SMT-LIB <tt>UninterpretedFuncTerm</tt>. If it is of
 * <tt>Sort</tt> BOOLEAN, it will be translated into an SMT-LIB <tt>UninterpretedPredFormula</tt>
 * <p>
 * The name of the uninterpreted function or predicate respectively is created out of the variable
 * name and an id unique to the <tt>ProgramVariable</tt>. It further consists of a prefix 
 * indicating that this is a translation of an <tt>ProgramVariable</tt> and a suffix that allows to
 * quickly distinguish functions from predicates and integer functions from object functions
 *  
 * @author akuwertz
 * @version 1.3,  03/28/2006  (Minor fixes)
 */

public class TranslateProgramVariable implements IOperatorTranslation {

    /* Additional fields */
    
    /** A cache for already translated <tt>ProgramVariable</tt> instances */
    private final HashMap translatedProgVars = new HashMap();
    
    /** A prefix used in the names of the uninterpreted functions and predicates respectively to
     * indicate that they represent a translations of an <tt>ProgramVariable</tt> */
    private static final String progVarPrefix = "ProgVar_";
    
    /** A suffix used in the name of the created uninterpreted function to indicate that it 
     * represents the translation of an integer <tt>ProgramVariable</tt> */
    private static final String progVarIntSuffix = "_int";
    /** A suffix used in the name of the created uninterpreted function to indicate that it 
     * represents the translation of an object <tt>ProgramVariable</tt> */
    private static final String progVarObjectSuffix = "_object";
    
    /** A suffix used in the name of the created uninterpreted function to mark it as function */
    private static final String progVarUifSuffix = "_UIF";
    /** A suffix used in the name of the created uninterpreted predicate to mark it as predicate */
    private static final String progVarUipSuffix = "_UIP";
    
    /** A <tt>Logger</tt> for logging and debugging operator translation */
    private static final Logger logger = Logger.getLogger( TranslateProgramVariable.class.getName() );
        // Logger is created hierarchical to inherit configuration and behaviour from parent
    
    /* String constants for error messages */
    private static final String unsupportedProgVar = "Translation of program variable failed: ";
    private static final String unsupportedProgVarFailure = "\nCaused by unsupported Sort: ";
    
    
    
    /* Public method implementation */
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.translation.IOperatorTranslation#isApplicable(de.uka.ilkd.key.logic.op.Operator)
     */
    public boolean isApplicable( Operator op ) {
        return op instanceof ProgramVariable; 
    }

    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.translation.IOperatorTranslation#translate(de.uka.ilkd.key.logic.op.Operator, de.uka.ilkd.key.proof.decproc.translation.TermTranslationVisitor)
     */
    public Object translate( Operator op, TermTranslationVisitor ttVisitor ) {
        
        Sort integerSort = ttVisitor.getServices().getTypeConverter().getIntegerLDT().targetSort();
        Sort booleanSort = ttVisitor.getServices().getTypeConverter().getBooleanLDT().targetSort();
        Sort currentSort = ((ProgramVariable) op).sort();
        Signature uiSig;
        String generatedConstName;
        
        // If the program variable has already been translated, return cached translation
        if ( translatedProgVars.containsKey( op ) ) {
            logger.info( "Found a previously translated program variable: " + op.name() );
            logger.info( "Returning cached translation for this program variable" );
            return translatedProgVars.get( op );
        }
        
        if ( currentSort.extendsTrans( integerSort )  ||  currentSort == booleanSort  ||
             currentSort instanceof ObjectSort ) {    
            logger.info( "Found program variable: " + op.name() );
            // Add a unique ID to the name of the uninterpreted function/predicate
            generatedConstName = progVarPrefix +
                                 SmtAufliaTranslation.legaliseIdentifier( op.name().toString() ) +
                                 "_" + translatedProgVars.size();
            Object translation;
            
            if ( currentSort.extendsTrans( integerSort )  ||
                 currentSort instanceof ObjectSort ) {
                // Program variables of integer or object sort are translated into uninterpreted
                // function constants
                generatedConstName += progVarUifSuffix;
                if ( currentSort.extendsTrans( integerSort ) ) {                
                    generatedConstName += progVarIntSuffix;
                    logger.info( "Found integer sort for this program variable, creating " +
                                 "uninterpreted function and caching it" );
                } else {
                    generatedConstName += progVarObjectSuffix;
                    logger.info( "Found object sort for this program variable, creating " +
                                 "uninterpreted function and caching it" );
                }
                logger.debug( "Function was given the name: " + generatedConstName );
                uiSig = Signature.constSignature( false );
                ttVisitor.createTypePredUif( currentSort , generatedConstName, 0 );
                translation = new UninterpretedFuncTerm( generatedConstName, null, uiSig );
                translatedProgVars.put( op , translation );
                
            } else {
                // Program variables of boolean sort are translated into uninterpreted predicates
                generatedConstName += progVarUipSuffix;
                uiSig = Signature.intSignature( 0 , false );
                logger.info( "Found boolean sort for this program variable, creating " +
                             "uninterpreted predicate and caching it" );
                logger.debug( "Predicate was given the name: " + generatedConstName );
                translation =  new UninterpretedPredFormula( generatedConstName, null, uiSig );
                translatedProgVars.put( op, translation );
            }
            
            return translation;
        }
        
        // The given program variable is of an untranslatable sort!
        logger.info( "Found unsupported program variable, exiting with exception!" );
        throw new UnsupportedOperationException( unsupportedProgVar + op.name() + 
                                                 unsupportedProgVarFailure + currentSort );
    }
}
