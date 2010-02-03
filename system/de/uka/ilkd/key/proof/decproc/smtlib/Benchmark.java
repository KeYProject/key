// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.decproc.smtlib;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Vector;


/** Represents a benchmark as defined in the SMT-Lib specification. 
 * <p>
 * A benchmark thereby represents a closed first order formula with additional information attached
 * to it. To be exact, the formula is built over a sublogic of first order logic with equality, 
 * namely (QF_)AUFLIA in this case.
 * <p>
 * The <tt>String</tt> representation of a <tt>Benchmark</tt> can be given to any decision 
 * procedure supporting the SMT-LIB format and the (QF_)AUFLIA sublogic, to decide satisfiability
 * of the represented formula.<br>
 * To get a <tt>String</tt> representation appropriate for SMT-LIB satisfiability solvers for an
 * arbitrary <tt>Formula</tt> (SMT-LIB), the <tt>setFormula</tt> method must be called on a 
 * <tt>Benchmark</tt> instance with that <tt>Formula</tt> as argument. Calling to <tt>toString</tt>
 * method on this <tt>Benchmark</tt> will then generate an appropriate <tt>String</tt>
 * representation
 * 
 * @author akuwertz
 * @version 1.3,  03/28/2006  (Minor fixes)
 * 
 * @see <a href="http://combination.cs.uiowa.edu/smtlib/">SMT-LIB</a>
 */

public class Benchmark {
    
    /** The name of this <tt>Benchmark</tt> */
    private final String bmName;
    /** The ":logic" attribute of this <tt>Benchmark</tt> */
    private String bmLogic;
    /** The ":source" attribute of this <tt>Benchmark</tt>; empty by default */
    private String source = "";
    /** The ":formula" attribute of this <tt>Benchmark</tt>, representing its <tt>Formula</tt> */
    private Formula formula;
    /** The assumptions of this <tt>Benchmark</tt> */  
    private Formula[] assumptions;
    /** The notes of this <tt>Benchmark</tt> */
    private String notes = "";
          
    /* The follow String variables represent the immutable pieces of a Benchmark, for 
     * internal use only */
    private static final String bmBegin  = "(benchmark ";
    private static final String bmDefaultName = "SmtAuflia_";
    private static final String 
        bmSource = "\n :source { Translated automatically from a KeY proof obligation.\n" +
                   "           The KeY project - Integrated Deductive Software Design:\n" +
                   "           Universitaet Karlsruhe, Germany\n" + 
                   "           Universitaet Koblenz-Landau, Germany\n" +
                   "           Chalmers University of Technology, Sweden\n" + 
                   "           => Visit http://www.key-project.org for more information\n" +
                   "         }\n\n";
    private static final String bmStatus = " :status unknown\n";
    private static final String bmLogicQF_AUFLIA  = " :logic QF_AUFLIA\n";
    private static final String bmLogicAUFLIA  = " :logic AUFLIA\n";
    private static final String bmExtraFun  = " :extrafuns ";
    private static final String bmExtraPred = " :extrapreds ";
    private static final String bmExtraSort = " :extrasort ";
    private static final String bmAssumption = " :assumption ";
    private static final String bmFormula    = " :formula ";
    private static final String bmNotesStart = "\n\n :notes \"";
    private static final String bmNotesEnd = " \"";
    private static final String bmEnd = "\n)";
    
    /* String constants for error messages during Benchmark creation */
    private static final String noFormulaSetError = "No formula has yet been set!";
    private static final String noLogicSetError = "No logic has yet been specified!";
    
    
    /* Constructor */ 
    
    /** Just a constructor
     * 
     * @param name the name of the <tt>Benchmark</tt> to be created. If the given <tt>String</tt>
     *        is <tt>null</tt>, the name is set to "SmtAuflia_Benchmark" by default 
     */
    public Benchmark( String name ) {
        bmName =  bmDefaultName + name;
        assumptions = new Formula[0];
    }
    
    
    
    /* Public method implementation */
    
    /** Sets the ":logic" attribute of this <tt>Formula</tt> by specifying if quantifiers should
     *  be supported or not
     *  @param useQuantifiers if true, quantifiers will be supported (AUFLIA); else QF_AUFLIA
     *                        will be used as logic
     */
    public void setLogic( boolean useQuantifiers ) {
        bmLogic = bmLogicAUFLIA;
        if ( ! useQuantifiers ) bmLogic = bmLogicQF_AUFLIA;  
    }

    /** Sets the <tt>Formula</tt> of this <tt>Benchmark</tt> to the specified <tt>Formula</tt>
     * 
     * @param f the <tt>Formula</tt> this <tt>Benchmark</tt> should represent
     */
    public void setFormula( Formula f ) {
        formula = f;
    }
    
    
    /** Returns the <tt>Formula</tt> of this <tt>Benchmark</tt>
     * 
     * @return the <tt>Formula</tt> of this <tt>Benchmark</tt>
     */
    public Formula getFormula() {
        return formula;
    }   
    

    /** Sets the assumptions of this Benchmark to the specified <tt>Formula</tt> array
     * @param assumptions the <tt>Formula</tt> array of assumptions under which the 
     *                    <tt>Formula</tt> of this <tt>Benchmark</tt> should be checked
     */
    public void setAssumptions( Formula[] assumptions ) {
       this.assumptions = assumptions;
    }
    
    
    /** Returns the assumptions of this <tt>Benchmark</tt>
     * 
     * @return a <tt>Formula</tt> array containing the assumptions under which the <tt>Formula</tt>
     *         of this <tt>Benchmark</tt> should be checked
     */         
    public Formula[] getAssuptions() {
        return assumptions;
    }
    
    
    /** Sets the notes of this Benchmark to the specified <tt>String</tt>
     * @param notes the <tt>String</tt> representing to value of the ":notes" attribute for
     *              this <tt>Benchmark</tt>
     */
    public void setNotes( String notes ) {
        this.notes = bmNotesStart + notes + bmNotesEnd;
    }
    
    /** Sets the ":source" attribute of this <tt>Benchmark</tt> to a predefined value.
     * <p>
     * Before this function is called on a <tt>Benchmark</tt> for the first time, it won't contain
     * any ":source" attribute 
     */ 
    public void setSource() {
        source = bmSource;
    }
    
    
    /** Returns a String representation of this <tt>Benchmark</tt>, including the String 
     * representations of its <tt>Formula</tt> and its extra uninterpreted functions. 
     * The returned representation satisfies the specifications of the SMT-Lib 
     * benchmark definition
     * 
     * @return The String representation of this <tt>Benchmark</tt>  
     * @throws IllegalStateException if this method is called on a <tt>Benchmark</tt> whichout
     *                               specifying its logic or setting its <tt>Formula</tt> first,
     *                               or if its <tt>Formula</tt> is set to <tt>null</tt> 
     */      
    public String toString() {

        if ( formula == null ) throw new IllegalStateException( noFormulaSetError );
        if ( bmLogic == null ) throw new IllegalStateException( noLogicSetError );
        
        // Assemble benchmark head
        String representation = bmBegin + bmName + source + bmStatus + bmLogic;

       // Assemble the ":extrafuns" , ":extrapreds" and ":extrasorts" attributes                 
       UninterpretedFuncTerm[] extraFuns = ( UninterpretedFuncTerm[] ) 
           formula.getUIF().toArray( new UninterpretedFuncTerm[formula.getUIF().size()] );
       Vector uiPred = formula.getUIPredicates();
       UninterpretedPredFormula[] extraPreds = ( UninterpretedPredFormula[] ) 
           uiPred.toArray( new UninterpretedPredFormula[ uiPred.size() ] );
       Set freeSorts = new HashSet();       
       // First ":extrafuns"
       String exFuncDefs = "";
       for ( int i = 0; i < extraFuns.length; i++ ) {
           // Add uninterpreted sorts           
           freeSorts.addAll( extraFuns[i].getSignature().getUiSorts() );           
           // Assemble ":extrafuns" attribute for each uninterpreted function
           exFuncDefs +=  bmExtraFun + "((" + extraFuns[i].getFunction() + " "
                        + extraFuns[i].getSignature().toString() + "))\n";
       }
       // Then ":extrapreds"
       String exPredDefs = "";
       for ( int i = 0; i < extraPreds.length; i++ ) {
           // Add uninterpreted sorts           
           freeSorts.addAll( extraPreds[i].getSignature().getUiSorts() );   
           // Assemble ":extrapreds" attribute for each uninterpreted predicate
           exPredDefs +=  bmExtraPred + "((" + extraPreds[i].getOp() + " "
                        + extraPreds[i].getSignature().toString() + "))\n";
       }
       // At last assemble ":extrasort" attribute for each of the collected sort strings
       String exSortDefs = "";
       Iterator sortIterator = freeSorts.iterator();
       while( sortIterator.hasNext() ) 
           exSortDefs += bmExtraSort + "((" +  ( String ) sortIterator.next() + "))\n";       
       
       // Assemble the ":assumption" attributes
       String allAssumptions = "";
       for ( int i = 0; i < assumptions.length; i++ ) {
           allAssumptions += bmAssumption + assumptions[i].toString() + "\n";
       }       
       
       // Assemble the ":formula" attribute
       String formulaAttr = bmFormula + formula.toString();
       
       // Attach the assembled attributes to the header and return the result
       representation += exSortDefs + exFuncDefs + exPredDefs + allAssumptions + formulaAttr + notes;  
       return representation + bmEnd;
    }
}
