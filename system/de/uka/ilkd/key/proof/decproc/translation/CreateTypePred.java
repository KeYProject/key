// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.decproc.translation;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Vector;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.decproc.DecisionProcedureSmtAufliaOp;
import de.uka.ilkd.key.proof.decproc.SmtAufliaTranslation;
import de.uka.ilkd.key.proof.decproc.smtlib.*;

/** This class is responsible for creating and managing type (guard) predicates
 * <p>
 * Type predicates are needed to support the SMT logic AUFLIA (quanitifier support). 
 * 
 * @author akuwertz
 * @version 1.1,  12/17/2006
 */

public class CreateTypePred {
    
    /** A <tt>Vector</tt> to store all type predicates created for uninterpreted functions */
    private final Vector createdTypePredsUif;
    
    /** A <tt>Set</tt> to store the names of all functions for which type predicates have 
     * already been created */
    private final Set typedUifNames;
    
    /** A <tt>boolean</tt> indicating if any quantified variables have been type guarded */
    boolean areVarsGuarded;
    
    /** A <tt>HashSet</tt> to store all occuring limiting sorts */
    private final HashSet limitingObjectSorts;
    
    /** A <tt>HashSet</tt> to store all occuring declaring sorts */
    private final HashSet declaringObjectSorts;
    
    /** The <tt>Services</tt> used during the current translation process */
    private final Services services;
    
    /** The Key <tt>Sort</tt> representing integer numbers */
    private final Sort integerSort;
        
    /** The common prefix for all created type predicates */
    private static final String typePredPrefix = "is_";
    
    /** The variable prefix for type predicates over non constants functions*/
    private static final String typePredQuantVar = "x_";
        
    /** The prefix for <tt>Array</tt> <tt>Sort<tt/>s used in predicate names */
    private static final String predNameArraySuffix = "_Array";
    
    /** A <tt>Logger</tt> for logging and debugging operator translation */
    private static final Logger logger = Logger.getLogger( CreateTypePred.class.getName() );
    
    
    /* String constants for error messages */
    private static final String argCountBelowZero = "Function arity must be non-negative!";
    
    
    
    /* Constructor */
    
    /** Just a mere constructor
     *  
     * @param services the <tt>Services</tt> used during current translation
     */ 
    public CreateTypePred( Services services ) { 
        this.services = services;
        integerSort = services.getTypeConverter().getIntegerLDT().targetSort();
        areVarsGuarded = false;
        createdTypePredsUif  = new Vector();
        typedUifNames        = new HashSet();
        declaringObjectSorts = new HashSet();
        limitingObjectSorts  = new HashSet();
        
    }
    
    
    
    /* Protected method implementation */
    
    /** Creates a type predicate for the given <tt>Sort</tt> with the given <tt>TermVariable</tt>
     * as argument.
     * <p>
     * The given <tt>Sort</tt> must be a fully qualified and therefore unique <tt>Sort</tt>
     * 
     * @param type the <tt>Sort</tt> to be represented by a type predicate
     * @param termVar the <tt>Term</tt> variable of <tt>Sort</tt> <tt>type</tt> to be represented
     * @return an <tt>UninterpretedPredFormula</tt> representing the specified type predicate
     */
    protected Formula getTypePredLv( Sort type, TermVariable termVar ) {
        // Collect sorts used as type guards. These can be instantiated by uninterpreted functions
        // of an appropriate (sub)sort!
        if ( type instanceof ObjectSort )  
            if ( limitingObjectSorts.add( type ) )
            logger.debug( "Found new limiting sort: " + type );
        
        String op;
        if ( type.extendsTrans( integerSort ) ) {
            // Treat all integer subsorts as integer!
            op = createPredName( integerSort );
        } else {
            op = createPredName( type );
        }
        // Return uninterpreted predicate: (type termVar)
        logger.info( "Created and returned new type predicate: " + op + " ... for term: "
                     + termVar );
        areVarsGuarded = true;
        return new UninterpretedPredFormula( op , new Term[]{ termVar } , 
                                             Signature.constSignature( false ) );
    }    
    
    
    /** Creates and internally stores a unique type predicate for the given <tt>Sort</tt> with the
     * given uninterpreted function as argument
     * <p>
     * The given <tt>Sort</tt> must be a fully qualified and therefore unique <tt>Sort</tt><br>
     * The given function name must be a legal identifier in AUFLIA (see UninterpretedFuncTerm)
     * 
     * @param type the <tt>Sort</tt> to be represented by a type predicate
     * @param funcName a <tt>String</tt> denoting the name of the <tt>UninterpretedFuncTerm</tt>
     *                 to be represented by the created type predicate 
     * @param args the arity of the specified uninterpreted function
     * 
     * @throws IllegalArgumentException if <tt>args</tt> is negative
     * 
     * @see UninterpretedFuncTerm
     */        
    protected void createTypePredUif( Sort type, String funcName, int args ) {
        if ( args < 0 ) throw new IllegalArgumentException( argCountBelowZero );
        // Check if type predicate for this function has already been created
        if ( ! typedUifNames.add( funcName ) ) return;
        // Collect sorts of occuring uninterpreted functions for possible type guard instantiation 
        if ( type instanceof ObjectSort )  
            if  ( declaringObjectSorts.add( type ) )          
                logger.debug( "Found new declaring sort: " + type );
        
        String op; 
        if ( type.extendsTrans( integerSort ) ) {
            // Treat all integer subsorts as integer!
            op = createPredName( integerSort );
        } else {
            op = createPredName( type );
        }
        // Prepare term variables for type predicate
        TermVariable[] quantVars = new TermVariable[ args ];
        for ( int i = 0; i < args; i++ ) {
            quantVars[i] = new TermVariable( typePredQuantVar + i, 
                                             Signature.constSignature( false ) );
        }
        // Prepare uninterpreted function with created term vars as arguments
        Term uif = new UninterpretedFuncTerm( funcName, quantVars, 
                Signature.intSignature( args, true ) );
        // Prepare uninterpreted type predicate
        Formula typePred = new UninterpretedPredFormula( op, new Term[] { uif } , 
                Signature.constSignature( false ) );
        
        if ( args == 0 ) createdTypePredsUif.add( typePred );
        else {
            // Compose and store quantified formula: forall termVars typePred( uif ( termVars ) )
            createdTypePredsUif.add( new QuantifierFormula( DecisionProcedureSmtAufliaOp.FORALL ,
                                                            quantVars , typePred ) );
        }
        logger.info( "Stored new type predicated: " + op + " ...for function: " + funcName );
    }
    
    
    /** Returns a <tt>Vector</tt> containing all hierarchy predicates needed for the current 
     * translation
     * <p>
     * The hierarchy predicates are calculated by searching for the most direct occuring 
     * supersort of each occuring sort.<br> 
     * All supersorts occuring in the current sequent must be present in the limitingObjectSorts
     * <tt>Set</tt> 
     * 
     * @return the <tt>Vector </tt> of created hierarchy predicates
     */
    protected Vector createObjHierarchyPreds() {
        logger.info( "Creating hierarchy predicates out of the currently stored " +
                     "type predicates..." );
        HashSet declaringSorts = (HashSet) declaringObjectSorts.clone();
        HashSet limitingSorts = (HashSet) limitingObjectSorts.clone();
        
        // Check if any quantified variables are guarded by type predicates. If not, return...
        if ( limitingSorts.isEmpty() ) {
            logger.debug( "No limiting sorts could be found -> no hierarchy preds needed!" );
            return new Vector();
        }
        
        JavaInfo javaInfo = services.getJavaInfo();
        // Remove the sort representing java.lang.object and the Null sort!
        declaringSorts.remove( javaInfo.getJavaLangObjectAsSort() );
        declaringSorts.remove( Sort.NULL );
        limitingSorts.remove( javaInfo.getJavaLangObjectAsSort() );
        
        // Prepare...
        Sort current;
        KeYJavaType javaType;
        KeYJavaType javaLangObject = javaInfo.getJavaLangObject();
        TermVariable[] varArr 
            = new TermVariable[]{ new TermVariable( "x" , Signature.constSignature( false ) ) }; 
        UninterpretedPredFormula typePredSub, typePredSuper;
        Signature sig = Signature.intSignature( 1, false );
        Formula hierarchyPred;
        Vector resHierarchyPreds = new Vector();
        HashSet[] currentlyIterated = { declaringSorts , limitingSorts };
        Iterator it;
        
        // ... and search the most direct supersort contained in limitingObjectSorts for 
        // each occuring sort!
        for ( int i = 0; i < 2; i++ ) {
             it = currentlyIterated[i].iterator();
             while ( it.hasNext() ) {
                 current = (Sort) it.next();
                 logger.debug( "Processing sort: " + current );
                 javaType = javaInfo.getSuperclass( javaInfo.getKeYJavaType( current ) );
                 while ( ! javaType.equals( javaLangObject )  &&    // Reached upper hierarchy end!
                         ! limitingSorts.contains( javaType.getSort() ) ) {
                     // Find contained superclass!
                     javaType = javaInfo.getSuperclass( javaType );
                 }
                 // Found appropriate superclass, generating predicate
                 logger.debug( "Found supersort: " + javaType.getSort() );
                 typePredSub   = new UninterpretedPredFormula( 
                                     createPredName( current ) , varArr , sig );
                 typePredSuper = new UninterpretedPredFormula( 
                                     createPredName( javaType.getSort() ), varArr, sig );
                 hierarchyPred = new ConnectiveFormula( DecisionProcedureSmtAufliaOp.IMP, 
                         new Formula[]{ typePredSub, typePredSuper } );
                 hierarchyPred = new QuantifierFormula( DecisionProcedureSmtAufliaOp.FORALL, 
                         varArr , hierarchyPred );
                 resHierarchyPreds.add( hierarchyPred );
             }          
        }
        logger.info( "Finished creation! Returning hierarchy predicates!" );
        return resHierarchyPreds;
    }
    
    
    /** Returns a <tt>Vector</tt> containing all type predicates created during the translation 
     * of the current term
     *          
     * @return the <tt>Vector </tt> of created type predicates
     */
    protected Vector getCreatedTypePreds() {
        if ( ! areVarsGuarded ) {
            logger.debug( "No quantified variables are type guarded ->no need for type preds!" );
            return new Vector();
        }
        logger.debug( "Returning stored type predicates!" );
        return (Vector) createdTypePredsUif.clone();
    }
    
    
    /** Private helper method to uniformly create a legal predicate name for a given <tt>Sort</tt>
     * <p>
     * Also converts array brackets to 'Array' keyword
     * 
     * @param type the <tt>Sort</tt> for which a type predicate should be created
     * @return a uniform predicate name legal to AUFLIA identifier restrictions
     */
    private String createPredName( Sort type ) {
        String typeName = type.toString();
        if ( type instanceof ArraySort ) {
            // Replace KeY array suffix
            typeName = typeName.substring( 0 , typeName.length() - 2 );
            typeName += predNameArraySuffix;
        }
        return typePredPrefix + SmtAufliaTranslation.legaliseIdentifier( typeName ); 
    }
    
}
