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

import de.uka.ilkd.key.logic.Term;

/** This class implements a visitor used to determine the translatability of KeY <tt>Term</tt>s 
 * into SMT-LIB <tt>Formula</tt>e.
 * <p>
 * This implementation is intended for KeY <tt>Term</tt>s of <tt>Sort</tt> <tt>Formula</tt>. To
 * determine if a given <tt>Term</tt> can be translated into SMT-LIB syntax, its 
 * <tt>execPretOrder</tt> method should be called with an instance of this class as argument.
 * The determined result can be fetched subsequently by the <tt>getTranslationResult</tt> method,
 * which in case of this class delivers a Boolean indicating the translatability
 * <p>
 * This class also provides a factory method that can be used to get an instance of this class.
 * It implements the singleton pattern and allows reusing the same visitor object for multiple
 * successive translations, in conjunction with the reset method
 * 
 * @author akuwertz
 * @version 1.4,  12/10/2006  (Introduced new superclass 'TranslationVisitor')
 */

public class PreTranslationVisitor extends TranslationVisitor {
    
    /* Additional fields */
    
    /** A <tt>PreTranslationVisitor</tt> instance serving as a singleton. It allows object reuse
     * and therefore saving memory */
    private static PreTranslationVisitor singleton = null;
    
    /** A <tt>boolean</tt> indicating if the singleton instance should translate quantifiers */
    private static boolean translateQuantifiers;
    
    
    /** A <tt>boolean</tt> flag indicating if the currently visited <tt>Term</tt> is considered
     * translatable into SMT-Lib syntax */
    private boolean isTranslatable;
    
    /** A <tt>boolean</tt> indicating if this <tt>PreTranslationVisitor</tt> instance translates 
     * quantifiers */
    private final boolean isTranslatingQuantifiers;
    
    
    
    /* Constructors */
    
    /** Sole constructor.
     * <p>
     * Creates a new <tt>PreTranslationVisitor</tt> and initialises it with the rules for all 
     * operators that can not be translated
     * 
     * @param useQuantifier boolean that determines whether quantifiers will be translated or not 
     */
    public PreTranslationVisitor( boolean useQuantifier ) { 
        
        // Create a prefix identifying this class for logging
        loggingSubclass = "Pre";
        
        // This list of rules must contain only these rules to handle untranslatable Term operators
        ListOfIOperatorTranslation trRules = SLListOfIOperatorTranslation.EMPTY_LIST;
        if ( ! useQuantifier ) {
            trRules = trRules.append( new TranslateQuantifier() )
                             .append( new TranslateLogicVariable() );
        }
        trRules = trRules.append( new TranslateIUpdateOperator() ).        
                          append( new TranslateModality() ).
                          append( new TranslateProgramMethod() ).
                          append( new TranslateMetavariable() );
        
        setTranslationRules(trRules);
        isTranslatable = true;
        isTranslatingQuantifiers = useQuantifier;
    }
    
    
    /** A factory method returning a <tt>PreTranslationVisitor</tt> instance.
     * <p>
     * This method uses the Singleton pattern. It is intended to enable the reuse of an already created
     * visitor object after a complete translation. Use this method to get an instance of 
     * <tt>PreTranslationVisitor</tt> if there is no need for concurrency.
     * <p>
     * To specify whether the returned instance should translate quantifiers or not, the 
     * <tt>setTranslateQuantifiers</tt> method must be called prior to calling this method
     *   
     * @return a <tt>PreTranslationVisitor</tt> instance.
     * 
     * @throws IllegalStateException if the cached <tt>PreTranslationVisitor</tt> instance is not
     *                               considered reusable at this point of time
     * 
     * @see TranslationVisitor#getInstance()
     * @see #setTranslateQuantifers(boolean)
     */
    public synchronized static TranslationVisitor getInstance() {
        if ( singleton == null  ||  singleton.isTranslatingQuantifiers != translateQuantifiers ) {
            logger.debug( "Creating and storing new PreTranslationVisitor" +
                                   " as singleton..." );
            singleton = new PreTranslationVisitor( translateQuantifiers );
        }
        if ( !singleton.isReusable() ) throw new IllegalStateException( NoReuseStateException );
        return singleton;
    }
    
    
    
    /* Now the protected and public methods */
    
    /** The visit method of this <tt>PreTranslationVisitor</tt>. Takes a <tt>Term</tt> and tries
     * to determine its translatability by its <tt>Operator</tt>
     *   
     * @see de.uka.ilkd.key.logic.Visitor#visit(de.uka.ilkd.key.logic.Term)
     */
    public void visit( Term t ) {
        if ( isTranslatable ) {
            logger.info( logThis( "Starting to check term for translatability..." ) );
            for ( int i = 0; i < translationRules.length; i++ ) {     
                if ( translationRules[i].isApplicable( t.op() ) ) {
                    logger.info( logThis(
                        "Found appliable rule: " + translationRules[i].getClass().getName()
                        .replaceAll( translationRules[i].getClass().getPackage().getName() + "." , "" )
                        + " - term is not translatable!" ) );
                    isTranslatable = false;
                    // Leave loop after successful translation
                    i = translationRules.length;
                }
            }
            logger.info(  logThis( "Finished checking term!" ) );
            logger.debug( logThis( "Checked term: " +  t.toString() ) );
        }    
    }

    
    /** Determines whether a <tt>PreTranslationVisitor</tt> instance retrieved by the 
     * <tt>getInstance</tt> method translated quantifiers or not
     *  
     * @param useQuantifiers specifies if quantifiers should be translated or not
     * 
     * @see #getInstance()
     */
    public static void setTranslateQuantifers ( boolean useQuantifiers ) {
        translateQuantifiers = useQuantifiers;   
    }
    
    
    /** Checks whether a given <tt>Term</tt> contains any free quantifiable variables
     * 
     * @param t the <tt>Term</tt> to be checked for free variable occurrences 
     * @return true if no free variables occur in <tt>t</tt>  
     */
    public boolean noFreeVariableOccurrences( Term t ) {
        if ( t.freeVars().size() != 0) {
            logger.info( logThis( "Found free variables in term: " + t ) );
            return false;
        }
        logger.info( logThis( "Checked for free variables - no occurences" ) );
        return true;
    }
           
    
    /** Returns true if the <tt>Term</tt> visited during the last pretranslation process
     * can be translated into SMT-Lib syntax.
     * <p>
     * A <tt>Term</tt> is considered translatable if it does not represent a <tt>Quantifier</tt>,  
     * a <tt>Metavariable</tt>, a <tt>Modality</tt> or an <tt>IUpdateOperator</tt> and does not
     * contain any subterm representing one of the above mentioned <tt>Operator</tt>s.
     * <p>
     * This method should not be called directly but only accessed via the 
     * <tt>getTranslationResult</tt> method 
     * 
     * @return a <tt>Boolean </tt> indicating if the currently visited <tt>Term</tt> is considered
     *         translatable into SMT-Lib syntax; otherwise false
     */
    protected Object getResult() {
        Boolean result = new Boolean( isTranslatable );
        isTranslatable = true;  // Reset to resuable state
        return result;
    }
    
    
    /** Returns true if this <tt>PreTranslationVisitor</tt> is ready for the next translation process
     * <p>
     * This holds if that translation process has finished and the <tt>getTranslationResult</tt>
     * method was called, or if the <tt>reset</tt> method has been called in an arbitrary state
     * 
     * @return true if this <tt>TranslationVisitor</tt> is ready to be reused; otherwise false
     */
    protected boolean isReusable() {
        return super.isReusable()  &&  isTranslatable;
    }

    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.translation.TranslationVisitor#reset()
     */
    public void reset() {
        super.reset();
        isTranslatable = true;
        logger.debug( logThis( "Reseted PreTranslationVisitor!" ) );
    }
    
}
