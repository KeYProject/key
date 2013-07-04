package de.uka.ilkd.key.symbolic_execution.strategy;

import org.eclipse.core.runtime.IPath;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.StatementContainer;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.util.ExtList;

/**
 * This{@link LineBreakpointStopCondition} represents a line breakpoint and is responsible to tell the debugger to stop execution when the respective
 * breakpoint is reached.
 * 
 * @author Marco Drebing
 */


public class LineBreakpointStopCondition extends AbstractBreakpointStopCondition {

   /**
    * Creates a new {@link LineBreakpointStopCondition}.
    * 
    * @param classPath the path of the class the associated Breakpoint lies within
    * @param lineNumber the line where the associated Breakpoint is located in the class
    * @param hitCount the hitCount for this Breakpoint, given by user
    * @param environment the environment the that the proof that should be stopped is working in
    * @param pm the {@link IProgramMethod} representing the Method which the Breakpoint is located at
    * @param proof the {@link Proof} that will be executed and should stop
    * @param parentCondition a {@link CompoundStopCondition} containing this {@link LineBreakpointStopCondition} and all other {@link LineBreakpointStopCondition} the associated {@link Proof} should use
    * @param condition the condition as given by the user
    * @param enabled flag if the Breakpoint is enabled
    * @param conditionEnabled flag if the condition is enabled
    * @param methodStart the line the containing method of this breakpoint starts at
    * @param methodEnd the line the containing method of this breakpoint ends at
    * @throws SLTranslationException if the condition could not be parsed to a valid Term
    */
   public LineBreakpointStopCondition(IPath classPath, int lineNumber, int hitCount, KeYEnvironment<?> environment, IProgramMethod pm, Proof proof, CompoundStopCondition parentCondition, String condition, boolean enabled, boolean conditionEnabled, int methodStart, int methodEnd) throws SLTranslationException {
      super(classPath, lineNumber, hitCount, environment, pm, proof, parentCondition,
            condition, enabled, conditionEnabled, methodStart, methodEnd);
   }

  

   /**
    * For a given {@link StatementContainer} this method computes the {@link StatementBlock} that contains all lines before the line the Breakpoint is at, including the line itself.
    * 
    * @param statementContainer the {@link StatementContainer} to build the block from
    * @return the {@link StatementBlock} representing the container without the line below the Breakpoint
    */
   @Override
   protected StatementBlock getStatementBlock(StatementContainer statementContainer) {
      //list of all statements
      ExtList nextResult=new ExtList();
      for(int i = 0; i<statementContainer.getStatementCount();i++){
         nextResult.add(statementContainer.getStatementAt(i));
      }
      //find last interesting statement
      for(int i = 0;i<nextResult.size();i++){
         if(!(((SourceElement) nextResult.get(i)).getEndPosition().getLine()<=lineNumber)){
            if(nextResult.get(i) instanceof StatementContainer){
               //go into inner scope
               nextResult.set(i, getStatementBlock((StatementContainer)nextResult.get(i)));
            }else{
               //cut below last interesting statement
               for(int j = nextResult.size()-1;j>=i;j--){
                  nextResult.remove(statementContainer.getChildAt(j));
               }
            }
         }
      }
      return new StatementBlock(nextResult);
   }

   
}
