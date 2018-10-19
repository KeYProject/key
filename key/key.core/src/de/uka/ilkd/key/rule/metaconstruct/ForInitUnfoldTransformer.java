package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.statement.LoopInit;
import de.uka.ilkd.key.java.visitor.CreatingASTVisitor;
import de.uka.ilkd.key.java.visitor.LoopInitASTVisitor;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

/**
 * Pulls the initializor out of a for-loop. Only receives
 * the init as a parameter, not the whole for-loop.
 * 
 * Example:
 * 
 * \pi for (init; guard; upd) body \omega
 * 
 * to:
 * 
 * \pi {
 *		init'
 * 		for(; guard; upd) body
 * } \omega
 * 
 * @author Benedikt Dreher
 */
public class ForInitUnfoldTransformer extends ProgramTransformer {
	 /** creates a typeof ProgramTransformer 
     * @param loop the instance of expression contained by 
     * the meta construct 
     */ 
    public ForInitUnfoldTransformer(LoopInit loopInit) {
    	super("forInitUnfoldTransformer", loopInit); 
    } 
    
    public ForInitUnfoldTransformer(ProgramSV programSV) {
    	super("forInitUnfoldTransformer", programSV); 
    } 

    /** 
     * performs the program transformation needed for symbolic
     * program transformation 
     * @return the transformated program
     */
	public ProgramElement transform(ProgramElement pe, Services services, SVInstantiations svInst) {
		Debug.assertTrue(pe instanceof LoopInit, "ForInitUnfoldTransformer cannot handle ", pe);
		
		final LoopInit astLoopInit  = (LoopInit) pe;
		final Statement[] loopInitStatementList = new Statement[astLoopInit.getInits().size()]; 
		
		for (int i = 0; i<loopInitStatementList.length; i++) {
		    loopInitStatementList[i] = astLoopInit.getInits().get(i);
		}
		
		return KeYJavaASTFactory.block(loopInitStatementList);
	} 
}
