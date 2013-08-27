package de.uka.ilkd.key.symbolic_execution.strategy;

import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.StatementContainer;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;


/**
 * This{@link KeYWatchpointStopCondition} represents a KeY watchpoint and is responsible to tell the debugger to stop execution when the respective
 * watchpoint evaluates its condition to true.
 * 
 * @author Marco Drebing
 */
public class KeYWatchpointStopCondition extends AbstractConditionalBreakpointStopCondition{
   
   /**
    * a flag to tell whether the condition should evaluate to true or just be satisfiable
    */
   private boolean suspendOnTrue;


   /**
    * Creates a new {@link AbstractConditionalBreakpointStopCondition}. Call setCondition immediately after calling the constructor!
    * 
    * @param classPath the path of the class the associated Breakpoint lies within
    * @param hitCount the number of hits after which the execution should hold at this breakpoint
    * @param environment the environment the that the proof that should be stopped is working in
    * @param pm the {@link IProgramMethod} representing the Method which the Breakpoint is located at
    * @param proof the {@link Proof} that will be executed and should stop
    * @param parentCondition a {@link CompoundStopCondition} containing this {@link LineBreakpointStopCondition} and all other {@link LineBreakpointStopCondition} the associated {@link Proof} should use
    * @param condition the condition as given by the user
    * @param enabled flag if the Breakpoint is enabled
    * @param conditionEnabled flag if the condition is enabled
    * @param methodStart the line the containing method of this breakpoint starts at
    * @param methodEnd the line the containing method of this breakpoint ends at
    * @param containerType the type of the element containing the breakpoint
    * @param suspendOnTrue the flag if the condition needs to evaluate to true or just be satisfiable
    * @throws SLTranslationException if the condition could not be parsed to a valid Term
    */
   public KeYWatchpointStopCondition(String classPath, int hitCount,
         SymbolicExecutionEnvironment<?> environment, Proof proof,
         CompoundStopCondition parentCondition, String condition,
         boolean enabled, boolean conditionEnabled, KeYJavaType containerType, boolean suspendOnTrue) throws SLTranslationException {
      super(classPath, hitCount, environment, null, proof, parentCondition, enabled, conditionEnabled, -1, -1, containerType);
      setSuspendOnTrue(suspendOnTrue);
      this.setCondition(condition);
   }
   
   @Override
   protected StatementBlock getStatementBlock(
         StatementContainer statementContainer) {
      return (StatementBlock) statementContainer;
   }
   
   @Override
   protected boolean isInScope(Node node) {
      return true;
   }
   
   @Override
   protected boolean conditionMet(RuleApp ruleApp, Proof proof, Node node)
         throws ProofInputException {
      if(suspendOnTrue){
         return super.conditionMet(ruleApp, proof, node);
      }else{
         Term negatedCondition = TermBuilder.DF.not(getCondition());
         //initialize values
         PosInOccurrence pio = ruleApp.posInOccurrence();
         Term term = pio.subTerm();
         term = TermBuilder.DF.goBelowUpdates(term);
         IExecutionContext ec = JavaTools.getInnermostExecutionContext(term.javaBlock(), proof.getServices());
         //put values into map which have to be replaced
         if(ec!=null){
            getVariableNamingMap().put(getSelfVar(), ec.getRuntimeInstance());
         }
         //replace renamings etc.
         OpReplacer replacer = new OpReplacer(getVariableNamingMap());
         Term termForSideProof = replacer.replace(negatedCondition);
         //start side proof
         Term toProof = TermBuilder.DF.equals(TermBuilder.DF.tt(), termForSideProof);
         Sequent sequent = SymbolicExecutionUtil.createSequentToProveWithNewSuccedent(node, ruleApp, toProof);
         ApplyStrategyInfo info = SymbolicExecutionUtil.startSideProof(proof, sequent, StrategyProperties.SPLITTING_DELAYED);
         return !info.getProof().closed();
      }
   }
   
   public boolean isSuspendOnTrue() {
      return suspendOnTrue;
   }
   
   public void setSuspendOnTrue(boolean suspendOnTrue) {
      this.suspendOnTrue = suspendOnTrue;
   }
}
