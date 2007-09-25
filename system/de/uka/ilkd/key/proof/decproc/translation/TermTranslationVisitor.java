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

import java.util.Vector;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.decproc.smtlib.Formula;
import de.uka.ilkd.key.proof.decproc.smtlib.TermVariable;

/** This class implements a visitor used to translate <tt>Term</tt>s in KeY into <tt>Formula</tt>e
 * in SMT-LIB.
 * <p>
 * This implementation is intended for KeY <tt>Term</tt>s of <tt>Sort</tt> <tt>Formula</tt>. To
 * translate a given <tt>Term</tt>, its <tt>execPostOrder</tt> method should be called with an
 * instance of this class as argument. The translation result can then be fetched using the
 * <tt>getTranslationResult</tt> method of this class.
 * <p>
 * Prior to translating a <tt>Term</tt> with this class, its translatability should be checked by
 * using the <tt>PreTranslationVisitor</tt> subclass.
 * <p>
 * This class also provides a factory method that can be used to get an instance of this class.
 * It implements the singleton pattern and allows reusing the same visitor object for multiple
 * successive translations
 * 
 * @author akuwertz
 * @version 1.5,  12/10/2006  (Introduced new superclass 'TranslationVisitor')
 */ 

public class TermTranslationVisitor extends TranslationVisitor {

    /* Additional fields */
    
    /** A <tt>TermTranslationVisitor</tt> instance serving as a singleton. It allows object reuse
     * and therefore saving memory */
    private static TermTranslationVisitor singleton = null;
    
    /** The <tt>Services</tt> currently used by the singleton instance */
    private static Services currentServices;
    
    /** A <tt>boolean</tt> indicating if the singleton instance should translate quantifiers */
    private static boolean translateQuantifiers;
    
    
    /** A Vector serving as a stack for already translated subterms */ 
    private Vector argumentStack = new Vector();
    
    /** The currently used instance of <tt>CreateTypePred</tt> */
    private CreateTypePred typePredCreator;
    
    /** The <tt>Term</tt> been currently translated by the <tt>visit</tt> method */
    private Term currentTerm = null;
    
    /** The <tt>Services</tt> used by this <tt>TermTranslationVisitor</tt> instance */
    private final Services usedServices;
    
    /** A <tt>boolean</tt> indicating if this <tt>TermTranslationVisitor</tt> instance translates 
     * quantifiers */
    private final boolean isTranslatingQuantifiers;
        
    
    
    /* String constants for failures during translation process */
    private static final String 
        stackCountException = "Argument stack contains less elements than: ";
    private static final String 
        internalStateCorruptedError = "Translation has been corrupted due to internal errors!";
    
    
    
    /* Constructors */
    
    /** Sole constructor.
     * <p>
     * Creates a new <tt>TermTranslationVisitor</tt> and initialises it with all known translation
     * rules.<br> 
     * If <tt>useQuantifier</tt> is set to <tt>true</tt>, KeY <tt>Term</tt>s containing 
     * quantifier operators will be translated; otherwise, they are declared untranslatable
     * 
     * @param services the common <tt>Services</tt> of the KeY prover
     * @param useQuantifier boolean that determines if quantifiers will be translated or not
     */
    public TermTranslationVisitor( Services services, boolean useQuantifier ) {
                
        usedServices = services;
        isTranslatingQuantifiers = useQuantifier;
        
        // Create a prefix identifying this class for logging 
        loggingSubclass = "ttVis";
            
        
        // This command adds all available translation rules to this visitor. They will be used in
        // its visit method by applying the first suitable rule to translate the given operator, so
        // consider rule order carefully!
        logger.info( logThis( "Creating new TermTranslationVisitor..." ) );
        ListOfIOperatorTranslation trRules = SLListOfIOperatorTranslation.EMPTY_LIST.    
                                             append( new TranslateJunctor() ).
                                             append( new TranslateIfThenElse() ).
                                             append( new TranslateEquality() );
        if ( useQuantifier ) {
            trRules = trRules.append( new TranslateQuantifier() )
                             .append( new TranslateLogicVariable() );
        }
        trRules = trRules.append( new TranslateFunction() ).
                          append( new TranslateAttributeOp() ).
                          append( new TranslateArrayOp() ).
                          append( new TranslateProgramVariable() ).
                          append( new TranslateUnknownOp() );
        
        logger.debug( logThis( "Setting translation rules" ) ); 
        this.setTranslationRules( trRules );
        
        // Initialize the type predicate creation class
        typePredCreator = new CreateTypePred( usedServices );
        
        
    }
    
    
    /** A factory method returning a <tt>TermTranslationVisitor</tt> instance.
     * <p>
     * This method uses the Singleton pattern. It is intended to enable the reuse of an already created
     * visitor object after a complete translation. Use this method to get an instance of 
     * <tt>TermTranslationVisitor</tt> if there is no need for concurrency 
     * <p>
     * A translation process is considered complete after its result has been fetched by the 
     * <tt>getTranslationResult</tt> method of this class
     * <p>
     * To specify whether the returned instance should translate quantifiers or not, the 
     * <tt>setTranslateQuantifiers</tt> method must be called prior to calling this method.<br>
     * To specify the <tt>Services</tt> the returned instance should use, the <tt>setServices</tt>
     * method must be called prior to calling this method
     * 
     * @return a <tt>TermTranslationVisitor</tt> instance
     * 
     * @throws NullPointerException if no <tt>Services</tt> have been set with <tt>setServices</tt>
     * @throws IllegalStateException if the cached <tt>TermTranslationVisitor</tt> instance is not
     *                               considered reusable at this point of time
     *                               
     * @see TranslationVisitor#getInstance()
     * @see #setTranslateQuantifers(boolean)
     * @see #setServices(Services)                              
     */
    public synchronized static TranslationVisitor getInstance() {
        if ( singleton == null  ||   singleton.isTranslatingQuantifiers != translateQuantifiers
                                || ! singleton.usedServices.equals( currentServices ) ) {
            logger.debug( "Storing created TermTranslationVisitor instance as singleton..." );
            singleton = new TermTranslationVisitor( currentServices, translateQuantifiers );
        }
        if ( !singleton.isReusable() ) throw new IllegalStateException( NoReuseStateException );
        return singleton;
    }
        
    
    
    /* Now the public methods */
    
    /** The visit method of this <tt>TermTranslationVisitor</tt>. Takes a <tt>Term</tt> and tries
     * to translate its <tt>Operator</tt> into SMT-LIB syntax.
     * <p>
     * The translation result is stored in an internal stack for further processing   
     *  
     * @see de.uka.ilkd.key.logic.Visitor#visit(de.uka.ilkd.key.logic.Term)
     * @see #getTranslationResult()
     */
    public void visit( Term t ) {
        logger.info( logThis( "Starting term translation..." ) );
        currentTerm = t;
        for ( int i = 0; i < translationRules.length; i++ ) {     
            if ( translationRules[i].isApplicable( t.op() ) ) {
                logger.info( logThis( 
                        "Appling rule: " + translationRules[i].getClass().getName().replaceAll(
                        translationRules[i].getClass().getPackage().getName() + "." , "" ) ) );
                argumentStack.add( translationRules[i].translate( t.op(), this ) );
                logger.info(  logThis( "Finished term translation!" ) );
                logger.debug( logThis( "Term: " +  currentTerm.toString() ) );
                logger.debug( logThis( "was translated into: " + argumentStack.lastElement() ) );
                // Leave loop after successful translation
                i = translationRules.length;
            }
        }
    }
    
    
    /** Determines whether a <tt>TermTranslationVisitor</tt> instance retrieved by the 
     * <tt>getInstance</tt> method translated quantifiers or not
     *  
     * @param useQuantifiers specifies if quantifiers should be translated or not
     * 
     * @see #getInstance()
     */
    public static void setTranslateQuantifers ( boolean useQuantifiers ) {
        translateQuantifiers = useQuantifiers;   
    }
    
    
    /** Sets the <tt>Services</tt> that should be used by a <tt>TermTranslationVisitor</tt> 
     * instance retrieved by the <tt>getInstance</tt> method
     *  
     * @param services <tt>Services</tt> to be used
     * 
     * @see #getInstance()
     */
    public static void setServices ( Services services ) {
        currentServices = services;
    }
    
    
    /** Empties the type predicate storages.<br>
     * All type predicates that have been created during <tt>Term</tt> translation processes since
     * either the creation of this instance or the last call to this method will be deleted
     */
    public void clearTypePreds() {
        typePredCreator = new CreateTypePred( usedServices );
    }


    /** Returns the translation of a (logic) <tt>Term</tt> of <tt>Sort</tt> <tt>Formula</tt>,
     * which was built by successive calls of the <tt>visit</tt> method through the 
     * <tt>execPostOrder</tt> method on this <tt>Term</tt>.<br>
     * Also resets this <tt>TermTranslationVisitor</tt> for further reuse, so that this method
     * can only be called once per <tt>Term</tt> translation
     *  
     * @return the translation of the <tt>Term</tt> on which the <tt>execPostOrder</tt> method 
     *         was called with this <tt>TermTranslationvisitor</tt> as argument                              
     */ 
    protected Object getResult() {
        if ( argumentStack.size() != 1 ) throw new Error( internalStateCorruptedError );
        // Reset this instance for reuse: empty argument stack...
        return ( Formula ) argumentStack.remove( 0 );
    }
    
        
    /** Returns a <tt>Vector</tt> containing all type predicates created during all <tt>Term</tt>
     * translation process since either to creation of this instance or the last call to the 
     * <tt>clearTypePreds</tt> method
     *          
     * @return the <tt>Vector </tt> of created type predicates
     * 
     * @throws IllegalStateException if this method is called during an unfinished translation
     *                               process or before any translation was initiated
     * @see #clearTypePreds()                              
     */
    public Vector getCreatedTypePreds() {
        if ( ! super.isReusable() ) {
            throw new IllegalStateException( translationNotFinishedException );
        }
        return typePredCreator.getCreatedTypePreds();
    }
    
    
   /** Returns a <tt>Vector</tt> containing all hierarchy predicates needed for the current 
     * translation.<br>
     * The current translation thereby means all <tt>Term</tt> translation processes since either
     * the creation of this instance or the last call to the <tt>clearTypePreds</tt> method
     * 
     *   
     * @return the <tt>Vector </tt> of created hierarchy predicates
     * 
     * @throws IllegalStateException if this method is called during an unfinished translation
     *                               process or before any translation was initiated
     * @see #clearTypePreds()                              
     */
    public Vector getHierarchyPreds() {
        if ( ! super.isReusable() ) {
            throw new IllegalStateException( translationNotFinishedException );
        }
        return typePredCreator.createObjHierarchyPreds();
    }
    
    
    /* Now some protected helper functions, mainly intended for package internal usage */
    
    /** Returns an <tt>Object</tt> array containing the translation of the last <tt>count</tt>
     * translated <tt>Term</tt>s.<br>
     * Thereby the latest translation has the highest index. All returned translations are removed
     * from their internal storage
     *   
     * @param count the number of translations that should be returned
     * @return an <tt>Object</tt> array containing the last <tt>count</tt> stored translations
     * 
     * @throws IndexOutOfBoundsException if count is higher than the count of currently stored 
     * 
     * @see #visit(Term)
     */ 
    protected Object[] getTranslatedArguments( int count ) {
        if ( count > argumentStack.size() ) {
            throw new IndexOutOfBoundsException( stackCountException + count );
        }
        // Get the last count translated Terms/Formulae 
        Object[] translatedArgs = new Object[ count ];
        for ( int i = count - 1; i >= 0; i-- ) {            
            translatedArgs[i] = argumentStack.remove( argumentStack.size() - 1 ); 
        }         
        return translatedArgs;
    }
    
    
    /** Translates a given <tt>LogicVariable</tt> into its SMT-LIB representation.
     * <p>
     * This method uses the same class to translate the given <tt>LogicVariable</tt> as the
     * <tt>visit</tt> method but can be applied to a single <tt>LogicVariable</tt> instead of
     * a whole <tt>Term</tt>.
     * 
     * @param lv the <tt>LogicVariable</tt> to be translated manually 
     * @return the SMT-LIB representation of the translated <tt>LogicVariable</tt>
     */
    protected TermVariable translateLvManually( LogicVariable lv ) {
        TermVariable translation = null;
        logger.info( logThis( "Starting manual logic variable translation: " + lv.name() ) );
        for ( int i = 0; i < translationRules.length; i++ ) {     
            if ( translationRules[i] instanceof TranslateLogicVariable ) {
                logger.info( logThis( 
                             "Appling rule: " + translationRules[i].getClass().getName().replaceAll(
                                     translationRules[i].getClass().getPackage().getName() +
                                     "." , "" ) ) );
                // Important: the translate method of class LogicVariable does not change
                //            the stack of this TermTranslationVisitor!
                translation = (TermVariable) translationRules[i].translate( lv, this );
                logger.info( logThis( "Finished manual logic variable translation!" ) );
                // Leave loop after successful translation
                i = translationRules.length;
            }
        }
        return translation;
    }
    
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.translation.CreateTypePred#getTypePredLv(de.uka.ilkd.key.logic.sort.Sort, de.uka.ilkd.key.proof.decproc.smtlib.TermVariable)
     */
    protected Formula createTypePredLv( Sort type, TermVariable termVar ) {
        return typePredCreator.getTypePredLv( type, termVar );
    }
    
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.translation.CreateTypePred#createTypePredUif(de.uka.ilkd.key.logic.sort.Sort, java.lang.String, int)
     */
    protected void createTypePredUif( Sort type, String funcName, int argCount ) {
        typePredCreator.createTypePredUif( type, funcName, argCount );
    }
    
    
    /** Returns the currently translated <tt>Term</tt>
     * 
     * @return the currently translated <tt>Term</tt>
     */
    protected Term getCurrentTerm() {
        return currentTerm;
    }
    
    
    /** Returns the KeY <tt>Services</tt> used for translation
     * 
     * @return the KeY <tt>Services</tt> used for translation
     */
    protected Services getServices() {
        return usedServices;
    }
        
    
    /** Returns true if this <tt>TermTranslationVisitor</tt> is ready for the next translation
     * process.
     * <p>
     * This holds under the following conditions:
     *  - This instance was in reusable state and no translation has yet been initiated
     *  - The <tt>reset</tt> was called in an arbitrary state
     *  - The current translation has finish and the <tt>getTranslationResult</tt> method was
     *    called on this instance
     * 
     * @return true if this <tt>TranslationVisitor</tt> is ready to be reused; otherwise false
     */
    protected boolean isReusable() {
        return super.isReusable()  &&  argumentStack.isEmpty();
    }
    
    
    /** Resets this <tt>TermTranslationVisitor</tt> for reuse.<br>
     * After execution of this method the state of this <tt>TermTranslationVisistor</tt> is
     * equals to that of a newly created <tt>TermTranslationVisitor</tt>
     */
    public void reset() {
        super.reset();
        if ( !argumentStack.isEmpty() ) argumentStack.clear();
    }
    
}   
