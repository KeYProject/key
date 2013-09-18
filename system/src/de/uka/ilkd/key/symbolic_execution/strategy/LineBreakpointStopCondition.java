package de.uka.ilkd.key.symbolic_execution.strategy;

import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;

/**
 * This{@link LineBreakpointStopCondition} represents a line breakpoint and is responsible to tell the debugger to stop execution when the respective
 * breakpoint is reached.
 * 
 * @author Marco Drebing
 */


public class LineBreakpointStopCondition extends AbstractLineBreakpointStopCondition {

   /**
    * Creates a new {@link LineBreakpointStopCondition}.
    * 
    * @param classPath the path of the class the associated Breakpoint lies within
    * @param lineNumber the line where the associated Breakpoint is located in the class
    * @param hitCount the hitCount for this Breakpoint, given by user
    * @param pm the {@link IProgramMethod} representing the Method which the Breakpoint is located at
    * @param proof the {@link Proof} that will be executed and should stop
    * @param condition the condition as given by the user
    * @param enabled flag if the Breakpoint is enabled
    * @param conditionEnabled flag if the condition is enabled
    * @param methodStart the line the containing method of this breakpoint starts at
    * @param methodEnd the line the containing method of this breakpoint ends at
    * @throws SLTranslationException if the condition could not be parsed to a valid Term
    */
   public LineBreakpointStopCondition(String classPath, int lineNumber, int hitCount, IProgramMethod pm, Proof proof, String condition, boolean enabled, boolean conditionEnabled, int methodStart, int methodEnd) throws SLTranslationException {
      super(classPath, lineNumber, hitCount, pm, proof,
            condition, enabled, conditionEnabled, methodStart, methodEnd, pm.getContainerType()); 
   }
}
