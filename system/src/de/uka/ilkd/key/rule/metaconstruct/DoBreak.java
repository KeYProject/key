// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.statement.Break;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/** 
 * This class performs a labeled break. This means
 * <code>
 *  l1:l2:{l3:{l4:{break l3;}} ...}  
 * </code>
 * becomes
 * <code>
 *  l1:l2:{...} 
 * </code>
 */
public class DoBreak extends ProgramTransformer {
    

     /** creates a do-break ProgramTransformer 
     * @param labeledBreak the LabeledStatement contained by 
     * the meta construct 
     */
    public DoBreak(LabeledStatement labeledBreak) {
	super("do-break", labeledBreak); 	
    }

    
    
    /** a helper method to perform the symbolic execution of the
     * doBreak metaconstruct. 
     * @param block the NonTerminalProgramElement to go through and
     * look for the label
     * @param breakLabel the Label the break statement marked
     */
    private ProgramElement doBreak(NonTerminalProgramElement  block, 
				   Label breakLabel, Break b) {

	if (block instanceof LabeledStatement) { 
	    // we enter a labeled block so we have to check the label
	    Label blockLabel = ((LabeledStatement)block).getLabel();
	    if (blockLabel.equals(breakLabel)) {
		// skip this block  
		return new StatementBlock(new ImmutableArray<Statement>
					  (new Statement[0])); 
	    } else {
		// we assume that the doBreak is only applied in case
		// of success. That is why we create a new
		// LabeledBlock here and why we assume that the body
		// of this LabeledStatement is a NonTerminalProgramElement
		return b;
	    }
	}
	return null;
    }    

    /** performs the program transformation needed for symbolic
     * program transformation 
     * @param services the Services with all necessary information 
     * about the java programs
     * @return the transformated program
     */
    public ProgramElement transform(ProgramElement pe,
					    Services services,
					    SVInstantiations insts) {	
	// get label of break
	//	ContextInstantiationEntry ctx = insts.getContextInstantiation();
// 	Break breakStmnt = (Break) PosInProgram.
// 	    getProgramAt(ctx.prefix(), pe);
	LabeledStatement lst = (LabeledStatement)pe;
	Break breakStmnt;
	if (lst.getChildAt(1) instanceof Break) {
	    breakStmnt = (Break) lst.getChildAt(1);
	} else {
	    breakStmnt = (Break) 
		((StatementBlock) lst.getChildAt(1)).getChildAt(0);
	}
	return doBreak((NonTerminalProgramElement)pe, breakStmnt.getLabel(),
		       breakStmnt);
    }
}
