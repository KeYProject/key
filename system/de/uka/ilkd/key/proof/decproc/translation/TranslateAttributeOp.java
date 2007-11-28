// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.logic.op.AttributeOp;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.decproc.SmtAufliaTranslation;
import de.uka.ilkd.key.proof.decproc.smtlib.*;

/** This class represents the translation rule for <tt>AttributeOp</tt>s.
 * <p>
 * Thereby the attribute represented by the <tt>AttributeOp</tt> has to be a 
 * <tt>ProgramVariable</tt>. If this attribute is of <tt>Sort</tt> INT or OBJECT, it will be
 * translated into an SMT-LIB <tt>UninterpretedFuncTerm</tt>. If it is of <tt>Sort</tt> FORMULA,
 * it will be translated into an SMT-LIB <tt>UninterpretedPredFormula</tt>.
 * <p>
 * The name of the uninterpreted function or predicate respectively is created out of the name of 
 * the attribute and an id unique to the <tt>AttributeOp</tt> to be translated. It further consists 
 * of a prefix indicating that it is a translation of an <tt>AttributeOp</tt> and a suffix that 
 * allows to quickly distinguish functions from predicates
 * 
 * @author akuwertz
 * @version 1.5,  12/13/2006  (Minor fixes for AUFLIA support)
 */

public class TranslateAttributeOp implements IOperatorTranslation {

    /* Additional fields */
    
    /** A cache for already translated <tt>AttributeOp</tt> instances */
    private final HashMap translatedAttrOps = new HashMap();
    
    /** A prefix used in the names of the uninterpreted functions and predicates respectively to
     * indicate that they represent a translations of an <tt>AttributeOp</tt> */
    private static final String attrOpPrefix = "AttrOp_";
    
    /** A suffix used in the name of the created uninterpreted function to indicate that it 
     * represents the translation of an integer attribute */
    private static final String attrOpIntSuffix = "_int";
    /** A suffix used in the name of the created uninterpreted function to indicate that it 
     * represents the translation of an object attribute */
    private static final String attrOpObjectSuffix = "_object";
    
    /** A suffix used in the name of the created uninterpreted function to mark it as function */
    private static final String attrOpUifSuffix = "_UIF";
    /** A suffix used in the name of the created uninterpreted predicate to mark it as predicate */
    private static final String attrOpUipSuffix = "_UIP";
    
    /** A <tt>Logger</tt> for logging and debugging operator translation */
    private static final Logger logger = Logger.getLogger( TranslateAttributeOp.class.getName() );
        // Logger is created hierarchical to inherit configuration and behaviour from parent
        
    /* String constants for error messages */
    private static final String translationFailure = 
        "Translation of attribute operator failed due to illegal arguments on visitor stack:\n";
    private static final String failureCause = 
        " expected an argument of class UninterpretedFuncTerm (SMT-LIB) and found the object:\n";
    private static final String unsupportedAttributOp =
        "Translation of attribute op failed because its Sort could not be handled by this class: ";
    private static final String unsupportedAttributeType = 
        "Translation of attribute op failed because the type of its attribute could not be handled:\nS";
    
    
    
    /* Public method implementation */
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.translation.IOperatorTranslation#isApplicable(de.uka.ilkd.key.logic.op.Operator)
     */
    public boolean isApplicable( Operator op ) {
        return op instanceof AttributeOp;
    }

    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.translation.IOperatorTranslation#translate(de.uka.ilkd.key.logic.op.Operator, de.uka.ilkd.key.proof.decproc.translation.TermTranslationVisitor)
     */
    public Object translate( Operator op, TermTranslationVisitor ttVisitor ) {
        
        logger.debug( "Popping 1 argument from stack" );
        Object[] args = ttVisitor.getTranslatedArguments( 1 );
        Term[] convArgs;
        
        // Check if attribute is a ProgramVariable
        IProgramVariable attribute = ((AttributeOp) op).attribute();
        Sort attrOpSort;
        if ( attribute instanceof ProgramVariable ) {
            logger.debug( "Operator is a program variable!" );
            attrOpSort = ((ProgramVariable) attribute).sort(); 
        } else throw new IllegalArgumentException( unsupportedAttributeType + op.name() + 
                                                   " has type: " + attribute.getClass() );
        
        Sort integerSort = ttVisitor.getServices().getTypeConverter().getIntegerLDT().targetSort();
        Sort booleanSort = ttVisitor.getServices().getTypeConverter().getBooleanLDT().targetSort();
        Signature uiSig;
        String generatedFuncName;
        
        if ( attrOpSort.extendsTrans( integerSort )  ||  attrOpSort == booleanSort  ||  
             attrOpSort instanceof ObjectSort ) {
            if ( args[0] instanceof UninterpretedFuncTerm  ||  args[0] instanceof TermVariable ) {
                
                // Add a unique ID to the name of the uninterpreted function/predicate
                if ( ! translatedAttrOps.containsKey( op ) ) {
                    generatedFuncName = attrOpPrefix + 
                                        SmtAufliaTranslation.legaliseIdentifier( attribute.name().
                                                toString() ) + 
                                        "_" + translatedAttrOps.size();
                    logger.debug( "Generated unique ID for attribute operator" );
                    translatedAttrOps.put( op, generatedFuncName );
                }
                generatedFuncName = (String) translatedAttrOps.get( op );
                logger.info( "Found attribute operator: " + generatedFuncName );
                convArgs = new Term[]{ (Term) args[0] };
                
                if ( attrOpSort.extendsTrans( integerSort )  ||
                      attrOpSort instanceof ObjectSort ) {
                    // Attribute operators of integer or object sort are translated into 
                    // uninterpreted functions
                    generatedFuncName += attrOpUifSuffix;
                    if ( attrOpSort.extendsTrans( integerSort ) ) {                
                        generatedFuncName += attrOpIntSuffix;
                        logger.info( "Found integer attribute, creating uninterpreted function" );
                    } else {
                        generatedFuncName += attrOpObjectSuffix;
                        logger.info( "Found object attribute, creating uninterpreted function" );
                    }
                    uiSig = Signature.intSignature( 1 , true ); 
                    logger.debug( "Function was given the name: " + generatedFuncName );
                    ttVisitor.createTypePredUif( attrOpSort , generatedFuncName, 1 );
                    return new UninterpretedFuncTerm( generatedFuncName, convArgs, uiSig );
                }
                
                // Translate attribute operator into an uninterpreted predicate
                generatedFuncName += attrOpUipSuffix;
                uiSig = Signature.intSignature( 1 , false );
                logger.info( "Found boolean attribute, creating uninterpreted predicate" );
                logger.debug( "Predicate was given the name: " + generatedFuncName );
                return new UninterpretedPredFormula( generatedFuncName, convArgs, uiSig );
            }
            
            // Argument term popped from stack has wrong type!
            throw new IllegalArgumentException( translationFailure + op.name() + 
                                                failureCause + args[0] );
        }
        
        // The given attribute operator is of an untranslatable sort!
        logger.info( "Found unsupported attribute operator, exiting with exception!" );
        throw new UnsupportedOperationException( unsupportedAttributOp + op.name() + 
                                                " Sort: " + attrOpSort );
    }
}
