// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.metaconstruct;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/** 
 * This class is used to perform program transformations needed 
 * for the symbolic execution of a loop. It unwinds the loop:
 * e.g. 
 * <code>
 * while ( i<10 ) {
 *   i++
 * }  
 * </code> becomes 
 * <code>
 * l1: { 
 *   if (i<10) { i++} 
 *        else break l1;
 * l2: {
 *   while ( i<10 ) {
 *     i++
 *   }
 * }}  
 * </code> becomes          
 */
public class UnwindLoop extends ProgramMetaConstruct {

    /** the outer label that is used to leave the while loop ('l1') */
    private final SchemaVariable outerLabel;
    /** the inner label ('l2') */
    private final SchemaVariable innerLabel;
    

    /** creates an unwind-loop ProgramMetaConstruct 
     * @param loop the LoopStatement contained by the meta construct 
     */
    public UnwindLoop(SchemaVariable innerLabel, SchemaVariable outerLabel, 
                      LoopStatement loop) {
	super("#unwind-loop", loop); 
        this.innerLabel = innerLabel;
        this.outerLabel = outerLabel;
    }

    /** performs the program transformation needed for symbolic
     * program transformation 
     * @param services the Services with all necessary information 
     * about the java programs
     * @param svInst the instantiations esp. of the inner and outer label 
     * @return the transformated program
     */
    public ProgramElement symbolicExecution(ProgramElement pe,
					    Services services,
					    SVInstantiations svInst) {
	if (!(pe instanceof LoopStatement)) {
	    return pe;
	}
	final LoopStatement originalLoop = (LoopStatement)pe;
                        
	final WhileLoopTransformation w = 
	    new WhileLoopTransformation(originalLoop,
					(ProgramElementName)
					svInst.getInstantiation(outerLabel),
					(ProgramElementName)
					svInst.getInstantiation(innerLabel));
	w.start();
	return w.result();
    }

    public SchemaVariable getInnerLabelSV() {        
        return innerLabel;
    }        

    public SchemaVariable getOuterLabelSV() {        
        return outerLabel;
    }        
}
