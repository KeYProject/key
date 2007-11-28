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

import org.apache.log4j.Logger;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;

/** This class representing a visitor intended to be used for the translation of KeY <tt>Term</tt>s.
 * <p>
 * The translate a <tt>Term</tt>, a <tt>TranslationVisitor</tt> instance will be passed to either 
 * the <tt>execPostOrder</tt> or the <tt>execPreOrder</tt> method of the given <tt>Term</tt>. 
 * These methods then call the <tt>visit</tt> method of the passed <tt>TranslationVisitor</tt> 
 * recursively, with the appropriate subterms of the given <tt>Term</tt> as arguments
 *
 * @author akuwertz
 * @version 1.0,  12/10/2006
 */

public abstract class TranslationVisitor extends Visitor {
    
    /* Additional fields */
    
    /** The array of translation rules represented by exactly one instance of an  
     * <tt>IOperatorTranslation</tt> subclass per rule. */ 
    protected IOperatorTranslation[] translationRules = null;
        
    /** A counter indicating the level in the AST of the top level <tt>Term</tt> on which the 
     * currently translated subterms occurs */
    private int level = -1;
            
    /** A <tt>Logger</tt> for logging and debugging the translation process */
    protected static final Logger logger = 
        Logger.getLogger( TranslationVisitor.class.getName() );
    
    /** A short <tt>String</tt> identifying the implementing <tt>TranslationVisitor</tt> subclass
     * which has produced the current log statement */
    protected String loggingSubclass;
    
    
    /* String constants for failures during translation process */
    private static final String 
        nothingTranslatedException = "No translation has been initiated up to now!";
    protected static final String translationNotFinishedException = 
        "The translation of the current Term has not finished yet!";
    protected static final String NoReuseStateException =
        "Previous translation didn't finish successfully or result has not been fetched yet!";
    
    
    
    /* Public method implementation */
    
    /** A factory method for returning an instance of a <tt>TranslationVisitor</tt> implementing
     * subclass. It therefore must be implemented in that subclass. 
     * <p>
     * This method intends the reuse of already created subclass instances.  Subclasses overriding
     * this method should therefore use the Singleton pattern, enabling time and memory savings.
     * <p>
     * To reuse <tt>TranslationVisitor</tt> instances, they have to be in a well-defined, resuable
     * state. To ensure this state, the <tt>isReusable</tt> should be called by an overriding
     * implementation.<br> 
     * To reset an instance to a reusable state, the <tt>reset</tt> method should be used
     * 
     * @return a <tt>TranslationVisitor</tt> instance
     * 
     * @see #isReusable()
     * @see #reset()
     */
    public synchronized static TranslationVisitor getInstance() {
        throw new UnsupportedOperationException();
    }
    
    
    /** The visit method of this <tt>TranslationVisitor</tt>. Takes a KeY <tt>Term</tt> and tries
     * to translate it
     * <p>
     * Has to be implemented by a specific subclass    
     *  
     * @see de.uka.ilkd.key.logic.Visitor#visit(de.uka.ilkd.key.logic.Term)
     */
    abstract public void visit( Term t );
    
    
    /** This method is intended to be called only by the <tt>execPostOrder</tt> method of
     * class <tt>de.uka.ilkd.key.logic.Term</tt>
     * 
     * @see de.uka.ilkd.key.logic.Visitor#subtreeEntered(de.uka.ilkd.key.logic.Term)
     */
    public final void subtreeEntered( Term subtreeRoot ) {
        logger.info( logThis( "->Subtree entered!" ) );
        if ( level == -1 ) {
            level = 1;
        } else {
            level++;
        }
    }


    /** This method is intended to be called only by the <tt>execPostOrder</tt> method of
     * class <tt>de.uka.ilkd.key.logic.Term</tt>
     * 
     * @see de.uka.ilkd.key.logic.Visitor#subtreeLeft(de.uka.ilkd.key.logic.Term)
     */
    public final void subtreeLeft( Term subtreeRoot ) {
        logger.info( logThis( "<-Subtree left!" ) );
        level--;
    }
    
    
    /** Returns the result of the translation process and resets this <tt>TranslationVisitor</tt>
     * for reuse.
     * <p>
     * The result is actually fetched by calling the <tt>getResult</tt> method of the implementing
     * subclass.
     * <p>
     * After calling this method, this <tt>TranslationVisitor</tt> instance is in reusable state.
     * 
     * @return the <tt>Object</tt> resulting from current <tt>Term</tt> translation
     * 
     * @throws IllegalStateException if this method is called during an unfinished translation
     *                               process or before any translation was initiated
     * @see #getResult()                              
     */
    public final Object getTranslationResult() {
        // A positive level value indicates an unfinished translation
        if ( level > 0 ) throw new IllegalStateException( translationNotFinishedException );
        // A negative level value indicates that no translation was initiated 
        if ( level < 0 ) throw new IllegalStateException( nothingTranslatedException );

        level = -1;  // Reset visitor for reuse
        
        logger.debug( logThis( "Visitor state is reusable, fetching result from subclass..." ) );
        return getResult();  // Provide a hook for subclasses
    }
    
    
    /** Resets this <tt>TranslationVisitor</tt> for reuse.<br>
     * After execution of this method, the state of this <tt>TranslationVisistor</tt> is equal
     * to that of a newly created <tt>TranslationVisitor</tt>
     */
    public void reset() {
        logger.info( logThis( "Reseted visitor!") );
        level = -1;
    }
    
    
    
    /* Protected (subclass) methods */
    
    /** Sets the translation rules by converting <tt>rules</tt> to an 
     * <tt>IOperatorTranslation</tt> array
     *  
     * @param rules the rules to be set 
     */
    protected final void setTranslationRules( ListOfIOperatorTranslation rules ) {
        translationRules = rules.toArray();
    }
    
    
    /** Returns true if this <tt>TranslationVisitor</tt> is ready for the next translation process
     * 
     * @return true if this <tt>TranslationVisitor</tt> is ready to be reused; otherwise false
     */
    protected boolean isReusable() {
        // A level value of -1 indicates that the previous translation process has completed
        return level == -1;
    }
    
    
    /** This methods provides a hook for implementing subclasses to forward their translation
     * results.
     * <p>
     * It is intended to be called exclusively by the <tt>getTranslationResult</tt> method
     * <p>
     * After calling this method on a <tt>TranslationVisitor</tt> subclass instance, the instance
     * has to be in the reusable state
     * 
     * @return the translation result provided by an implementing subclass
     * 
     * @see #getTranslationResult()
     */
    abstract protected Object getResult();
    
    
    /** Take a <tt>String</tt> which should be logged and adds a subclass identifying tag to it
     * 
     * @param toLog the <tt>String</tt> to be logged
     * @return the given <tt>String</tt> extended by a subclass tag 
     */
    protected final String logThis( String toLog ) {
        return "(" + loggingSubclass + ") " + toLog;
    }

}
