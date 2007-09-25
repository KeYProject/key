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

import java.math.BigInteger;
import java.util.HashMap;
import java.util.HashSet;
import org.apache.log4j.Logger;
import de.uka.ilkd.key.logic.op.DecisionProcedureSmtAufliaOp;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.decproc.SmtAufliaTranslation;
import de.uka.ilkd.key.proof.decproc.TypeBoundTranslation;
import de.uka.ilkd.key.proof.decproc.smtlib.*;

/** This class represents the translation rule for <tt>Function</tt>s.
 * <p>
 * There are several classes of KeY <tt>Function</tt>s that are translated diffenently:
 * <ul>
 * <li>ADD, SUB, NEG and the linear MUL are translated into SMT-LIB <tt>InterpretedFunction</tt>s</li>
 * <li>GT, GEQ, LT and LEQ are translated into SMT-LIB <tt>PredicateFormula</tt>e</li>
 * <li>inBYTE, inSHORT, inINT, inLONG and inCHAR are translated into a <tt>ConnectiveFormula</tt> 
 *     consisting of two LT-<tt>PredicateFormula</tt></li>
 * <li>Type boundaries like int_MIN, int_MAX, int_RANGE, int_HALFRANGE, ... (same for byte, short,
 *     long and char) are translated into a <tt>NumberConstantTerm</tt> or a 
 *     <tt>InterpretedFuncTerm</tt>s if they represent a negative value<li> 
 * <li>TRUE and FALSE as constant <tt>Function</tt>s of <tt>Sort</tt> boolean are translated into
 *     <tt>TruthValueFormula</tt>s</li>
 * <li><tt>Function</tt> symbols like #, Z, C, NEGLIT and 0..9, which represent number and character
 *     constants in KeY, are parsed and translated into an SMT-LIB <tt>NumberConstantTerm</tt>
 *     or an <tt>InterpretedFuncTerm</tt>, if the constants are negative</li>    
 * <li>All further <tt>Function</tt>s of <tt>Sort</tt> INT or OBJECT are translated into SMT-LIB 
 *     <tt>UninterpretedFuncTerm</tt>s</li>
 * <li>All further <tt>Function</tt>s of <tt>Sort</tt> <tt>FORMULA</tt> or BOOLEAN are translated
 *    into SMT-LIB <tt>UninterpretedPredFormula</tt>e</li>
 * </ul>
 * All uninterpreted function and predicate names consists of a prefix indicating that they 
 * represent translations of a  <tt>Function</tt> and a suffix allowing to quickly distinguish
 * between uninterpreted functoins and predicates
 *         
 * @author akuwertz
 * @version 1.4,  11/10/2006  (Added type predicates for uninterpreted functions)
 */

public class TranslateFunction implements IOperatorTranslation {

    /* Additional fields */
            
    /** A prefix used in the names of the uninterpreted functions and predicates respectively to
     * indicate that they represent the translation of a <tt>Function</tt> */
    private static final String funcPrefix = "Func_";
    
    /** A suffix used in the name of the created uninterpreted function to indicate that it 
     * represents the translation of an integer attribute */
    private static final String funcIntSuffix = "_int";
    /** A suffix used in the name of the created uninterpreted function to indicate that it 
     * represents the translation of an object attribute */
    private static final String funcObjectSuffix = "_object";
    
    /** A suffix used in the name of the created uninterpreted function to mark it as function */
    private static final String funcUifSuffix = "_UIF";
    /** A suffix used in the name of the created uninterpreted predicate to mark it as predicate */
    private static final String funcUipSuffix = "_UIP";
    
    /** A <tt>HashMap</tt> containing the translation of all functions having interpreted 
     * equivalents in SMT-LIB */
    private static final HashMap interpredFuncs = new HashMap( 4, 1 );
    /** A <tt>HashMap</tt> containing the translation of all comparative predicates */
    private static final HashMap compPreds = new HashMap( 4, 1 );
    /** A <tt>HashSet</tt> containing the names of all type boundary predicates */
    private static final HashSet typeBoundPreds = new HashSet( 8 );
    /** A <tt>HashSet</tt> containing the <tt>String</tt> representations of all type boundaries */
    private static final HashSet typeBounds = new HashSet( 32 );
    
    /** The common prefix of type boundary predicates */
    private static final String typePredPrefix = "in";
    /** The common suffix of the mininum type boundary */
    private static final String typeBoundMinSuffix = "_MIN";
    /** The common suffix of the maximum type boundary */
    private static final String typeBoundMaxSuffix = "_MAX";
    
    /** A cache for <tt>BigInteger</tt> instances using during number constant translation */
    private static final BigInteger[] cachedBigInts = new BigInteger[11];
    
    
    /** A <tt>Logger</tt> for logging and debugging operator translation */
    private static final Logger logger = Logger.getLogger( TranslateFunction.class.getName() );
        // Logger is created hierarchical to inherit configuration and behaviour from parent
    
    
    /* String constants for error messages */
    private static final String translationFailure = 
        "Translation of function failed due to illegal arguments on visitor stack:\n";
    private static final String failurerCauseNoTerm = 
        " expected an argument of class Term (SMT-LIB) and found the object:\n";
    private static final String failureCauseNoBigInt = 
        " expected an argument of class BigInteger and found the object:\n";
    private static final String unsupportedFunction = "Translation of function failed: ";
    private static final String unsupportedFunctionFailure = "\nCaused by unsupported Sort: "; 
        
    
    /** Just a mere constructor. */
    public TranslateFunction() {
        
        // Set translations for functions having interpreted equivalents        
        interpredFuncs.put( "add" , DecisionProcedureSmtAufliaOp.PLUS );
        interpredFuncs.put( "sub" , DecisionProcedureSmtAufliaOp.MINUS );
        interpredFuncs.put( "neg" , DecisionProcedureSmtAufliaOp.UMINUS );
        interpredFuncs.put( "mul" , DecisionProcedureSmtAufliaOp.MULT );
        
        // Set translations for comparative predicates
        compPreds.put( "gt"  , DecisionProcedureSmtAufliaOp.GT );
        compPreds.put( "geq" , DecisionProcedureSmtAufliaOp.GEQ );
        compPreds.put( "lt"  , DecisionProcedureSmtAufliaOp.LT );
        compPreds.put( "leq" , DecisionProcedureSmtAufliaOp.LEQ );
        
        // Initialise set of type boundary predicates
        final String[] typePredsArray = { "inByte" , "inShort" , "inInt" , "inLong" , "inChar" };
        for( int i = 0; i < typePredsArray.length; i++ ) typeBoundPreds.add( typePredsArray[ i ] );
        
        // Initialise set of type boundary strings
        final String[] typeBoundsArray = 
            {   "int_MIN" ,   "int_MAX" ,   "int_HALFRANGE" ,   "int_RANGE" , 
               "char_MIN" ,  "char_MAX" ,                      "char_RANGE" ,
               "long_MIN" ,  "long_MAX" ,  "long_HALFRANGE" ,  "long_RANGE" ,
               "byte_MIN" ,  "byte_MAX" ,  "byte_HALFRANGE" ,  "byte_RANGE" ,
              "short_MIN" , "short_MAX" , "short_HALFRANGE" , "short_RANGE" };
        for( int i = 0; i < typeBoundsArray.length; i++ ) typeBounds.add( typeBoundsArray[ i ] );
    }
    
    
    
    /* Public method implementation */

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.translation.IOperatorTranslation#isApplicable(de.uka.ilkd.key.logic.op.Operator)
     */
    public boolean isApplicable( Operator op ) {
        return op instanceof Function;
    }

    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.translation.IOperatorTranslation#translate(de.uka.ilkd.key.logic.op.Operator, de.uka.ilkd.key.proof.decproc.translation.TermTranslationVisitor)
     */
    public Object translate( Operator op, TermTranslationVisitor ttVisitor ) {
        
        Object[] args;
        Term[] convArgs;
        String opName = op.name().toString();
        
        // First terms which are translated into interpreted functions       
        if ( interpredFuncs.containsKey( opName ) ) {
            logger.info( "Found '" + opName + "' function, starting operator translation..." );
            logger.debug( "Popping " + op.arity() + " argument terms from stack" );
            args = ttVisitor.getTranslatedArguments( op.arity() );
            convArgs = new Term[ op.arity() ];
            for ( int i= 0; i < op.arity(); i++ ) {
                if ( args[i] instanceof Term ) convArgs[i] = (Term) args[i];
                else throw new IllegalArgumentException ( translationFailure + op.name() + 
                                                          failurerCauseNoTerm + args[i] );
            }    
            // Non linear multiplication must be treated as uninterpreted function
            if ( opName == "mul"  &&  !( args[0] instanceof NumberConstantTerm  ||
                 args[1] instanceof NumberConstantTerm ) ) {
                Signature sig = Signature.intSignature( 2, true );
                logger.info( "Creating uninterpreted (nonlinear) multiply function" );
                String funcName = funcPrefix + "non_linear_mult" + funcUifSuffix + funcIntSuffix;
                ttVisitor.createTypePredUif( ttVisitor.getCurrentTerm().sort() , funcName, 2 );
                return new UninterpretedFuncTerm( funcName , convArgs, sig );
            }
            String transOp = (String) interpredFuncs.get( opName );
            logger.info( "Creating '" + transOp + "' function" );
            return new InterpretedFuncTerm( transOp, convArgs );
        }
        
        
        // Now the comparative predicates
        if ( compPreds.containsKey( opName ) ) {
            logger.info( "Found predicate, starting operator translation..." );
            logger.debug( "Popping 2 argument terms from stack" );
            args = ttVisitor.getTranslatedArguments( 2 );
            if ( args[0] instanceof Term  &&  args[1] instanceof Term ) { 
                convArgs = new Term[] { (Term) args[0], (Term) args[1] };
                logger.info( "Creating '" + opName + "' predicate" );
                return new PredicateFormula( (String) compPreds.get( opName ) , convArgs );
            }
            throw new IllegalArgumentException ( errorMsg( args, opName ) );
        }
        
        
        // Now the predicates for data type boundaries
        if ( typeBoundPreds.contains( opName ) ) {
               logger.info( "Found predicate, starting operator translation..." );
               logger.debug( "Popping 1 argument term from stack" );
               args = ttVisitor.getTranslatedArguments( 1 );
               if ( args[0] instanceof Term ) { 
                   logger.info( "Found " + opName + " predicate" );
                   Term[] minArgs, maxArgs;
                   BigInteger value;
                   Term minBoundValue, maxBoundValue;
                   // Parse opName to get the type (replace "in")
                   String typeName = opName.replaceFirst( typePredPrefix , "" ).toLowerCase();
                   // Assemble type bound strings from parsing result and translate them into terms
                   value = new BigInteger( TypeBoundTranslation.getTypeBoundValue( 
                                               typeName + typeBoundMinSuffix ) );
                   minBoundValue = getTermRepresentation( value );
                   value = new BigInteger( TypeBoundTranslation.getTypeBoundValue( 
                                               typeName + typeBoundMaxSuffix ) );
                   maxBoundValue = getTermRepresentation( value );
                   minArgs = new Term[] { minBoundValue , (Term) args[0] };
                   maxArgs = new Term[] { (Term) args[0] , maxBoundValue };
                   logger.info( "Creating two 'leq' predicates, connected by an 'and' connective" );
                   PredicateFormula minConstraint = 
                       new PredicateFormula( DecisionProcedureSmtAufliaOp.LEQ, minArgs );
                   PredicateFormula maxConstraint = 
                       new PredicateFormula( DecisionProcedureSmtAufliaOp.LEQ, maxArgs );
                   Formula[] transParts = new Formula[] { minConstraint, maxConstraint };
                   return new ConnectiveFormula( DecisionProcedureSmtAufliaOp.AND, transParts );
               }
               throw new IllegalArgumentException();
        }
        
        
        // Now the type boundaries theirselves
        if ( typeBounds.contains( opName ) ) {
            logger.info( "Found type boundary '" + opName + "', creating number constant term" );
            BigInteger value = new BigInteger( TypeBoundTranslation.getTypeBoundValue( opName ) );
            return getTermRepresentation( value );
        }
         
        
        // Now the boolean constants
        if ( opName.equals( "TRUE" )  ||  opName.equals( "FALSE" ) ) {
            logger.info( "Found '" + opName + "' function, " +
                         "creating '" + opName.toLowerCase() + "' formula" );
            return TruthValueFormula.getInstance( opName.equals( "TRUE" ) );
        }     
        
        
        // Now number and character constants
        
        if ( opName.equals( "#" ) ) {
            // Start translation of number constant
            // Return zero to allow unique treatment of operator names representing digits
            logger.info( "Found '#' function, starting number constant translation with BigInteger" +
                         "constant 0 ... " );
            return BigInteger.ZERO; 
        }
        
        if ( opName.length() == 1  &&  opName.charAt(0) >= '0'  &&  opName.charAt(0) <= '9' ) {
            logger.info( "Found number constant, starting to process it..." );
            logger.debug( "Popping 1 BigInteger from stack" );
            args = ttVisitor.getTranslatedArguments( 1 );
            if ( args[0] instanceof BigInteger ) {
                BigInteger value = ((BigInteger) args[0]).multiply( getBigInt( 10 ) );
                logger.info( "Creating BigInteger for calculated result" );
                return value.add( getBigInt( opName.charAt(0) - '0' ) );
            }
            throw new IllegalArgumentException ( translationFailure + op.name() + 
                                                 failureCauseNoBigInt + args[0] );
        }
        
        if ( opName.equals( "neglit" ) ) {
            logger.info( "Found 'neglit' function, starting operator translation" );
            logger.debug( "Popping 1 BigInteger from stack" );
            args = ttVisitor.getTranslatedArguments( 1 );
            if ( args[0] instanceof BigInteger ) {
                logger.info( "Creating negated BigInteger" );
                return ((BigInteger) args[0]).negate();
            }
            throw new IllegalArgumentException ( translationFailure + op.name() + 
                                                 failureCauseNoBigInt + args[0] );
        }
        
        if ( opName.equals( "Z" )  ||  opName.equals( "C" ) ) {
            // These symbols indicate the end of the number/character constants
            // They are treated in the same way, i.e. character constants also become integers
            String constantType = opName.equals( "Z" ) ? "number" : "character";
            logger.info( "Found '" + opName + "' function," +
                         " finalizing " + constantType + " constant translation..." );
            logger.debug( "Popping 1 BigInteger from stack" );
            args = ttVisitor.getTranslatedArguments( 1 );
            if ( args[0] instanceof BigInteger ) {
                // Create SMT-LIB representation for the parsed number/character constant
                logger.info( "Creating term representation for processed " +
                             constantType + " constant" );
                return getTermRepresentation( (BigInteger) args[0] );
            }
            throw new IllegalArgumentException ( translationFailure + op.name() + 
                                                 failureCauseNoBigInt + args[0] );
        }
        
        
        // Last but not least all remaining function operaters are translated into uninterpreted 
        // predicates and functions respectively
        
        logger.info( "Found unknown function, starting function translation..." );
        logger.debug( "Popping " + op.arity() + " argument terms from stack" );
        args = ttVisitor.getTranslatedArguments( op.arity() );
        Sort integerSort = ttVisitor.getServices().getTypeConverter().getIntegerLDT().targetSort();
        Sort booleanSort = ttVisitor.getServices().getTypeConverter().getBooleanLDT().targetSort();
        Sort currentTermSort = ttVisitor.getCurrentTerm().sort();
        
        if ( currentTermSort.extendsTrans( integerSort )  ||  currentTermSort instanceof ObjectSort  ||
             currentTermSort == booleanSort  ||  currentTermSort == Sort.FORMULA ) {
            String generatedName = funcPrefix + SmtAufliaTranslation.legaliseIdentifier( opName );
            convArgs = new Term[ op.arity() ]; 
            for ( int i = 0; i < op.arity(); i++ ) {
                if ( args[i] instanceof Term ) convArgs[i] = (Term) args[i];
                else throw new IllegalArgumentException( translationFailure + opName + 
                                                         failurerCauseNoTerm + args[i] );
            }
            // Every operator of Sort int or object is translated into an uninterpreted function
            if ( currentTermSort.extendsTrans( integerSort ) ||
				 currentTermSort instanceof ObjectSort ) {    
                generatedName += funcUifSuffix;
                if ( currentTermSort.extendsTrans( integerSort ) ) {
                    logger.info( "Function has integer sort, creating uninterpreted function" );
                    generatedName += funcIntSuffix; 
                } else {
                    logger.info( "Function has object sort , creating uninterpreted function" );
                    generatedName += funcObjectSuffix; 
                }
                ttVisitor.createTypePredUif( currentTermSort, generatedName, op.arity() );
                Signature uiSig = Signature.intSignature( op.arity(), true );
                return new UninterpretedFuncTerm( generatedName, convArgs, uiSig );
            }
            // Operators of Sort FORMULA or boolean are translated into an uninterpreted predicate
            logger.info( "Function has sort '" + currentTermSort + "' ," +
                         " creating uninterpreted predicate" );
            Signature uiSig = Signature.intSignature( op.arity(), false );
            generatedName += funcUipSuffix;
            return new UninterpretedPredFormula( generatedName, convArgs, uiSig );   
        }
        
        // The given function is of an untranslatable sort!
        logger.info( "Found unsupported function, exiting with exception!" );
        throw new UnsupportedOperationException ( unsupportedFunction + opName + 
                                                  unsupportedFunctionFailure + currentTermSort );
    }
    
    
    
    /* Private helper methods */
    
    /** Returns a cached <tt>BigInteger</tt> instance representing the specified <tt>int</tt>
     * @param number the value which the returned <tt>BigInteger</tt> should represent
     * @return  a cached <tt>BigInteger</tt> instance
     * 
     * @throws IndexOutOfBoundsException if <tt>number</tt> is negative or greater than 10 
     */
    private BigInteger getBigInt( int number ) {
        if ( cachedBigInts[ number ] == null ) {
            cachedBigInts[ number ] = new BigInteger( "" + number );
        }
        return cachedBigInts[ number ];
    }
    
    
    /** Returns an SMT-LIB <tt>Term</tt> representing the given <tt>BigInteger</tt>
     *
     * @param value the number value to be represented in SMT-LIB syntax
     * @return a <tt>NumberConstantTerm</tt> or an <tt>InterpretedFuncTerm</tt> ( if value < 0!)
     *         as representation of the given number value
     */
    private Term getTermRepresentation( BigInteger value ) {
        Term representation = NumberConstantTerm.getInstance( value.abs() );
        if ( value.signum() == -1 ) {
            representation = new InterpretedFuncTerm( DecisionProcedureSmtAufliaOp.UMINUS,
                                                      new Term[] { representation } );
        }
        return representation;
    }
    
    
    /** Helper function to generate specific error message 
     * @param args the <tt>Object</tt> array of arguments for the translation  
     * @param opName the name of the <tt>Function</tt> to be translated on which the error occured
     * @return a <tt>String</tt> representing a specific error message 
     */
    private String errorMsg( Object[] args, String opName ) {
        String errorMsg = translationFailure + opName + failurerCauseNoTerm; 
        return errorMsg + ( (args[0] instanceof Term) ? args[1] : args[0] );   
    }
}
