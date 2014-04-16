package de.uka.ilkd.key.symbolic_execution.strategy;

import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.SourceElement;
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
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;


/**
 * This{@link KeYWatchpointStopCondition} represents a KeY watchpoint and is responsible to tell the debugger to stop execution when the respective
 * watchpoint evaluates its condition to true.
 * 
 * @author Marco Drebing
 */
public class KeYWatchpointStopCondition extends ConditionalBreakpointStopCondition{
   /**
    * a flag to tell whether the condition should evaluate to true or just be satisfiable
    */
   private boolean suspendOnTrue;

   /**
    * Creates a new {@link ConditionalBreakpointStopCondition}. Call setCondition immediately after calling the constructor!
    * 
    * @param hitCount the number of hits after which the execution should hold at this breakpoint
    * @param pm the {@link IProgramMethod} representing the Method which the Breakpoint is located at
    * @param proof the {@link Proof} that will be executed and should stop
    * @param condition the condition as given by the user
    * @param enabled flag if the Breakpoint is enabled
    * @param conditionEnabled flag if the condition is enabled
    * @param containerType the type of the element containing the breakpoint
    * @param suspendOnTrue the flag if the condition needs to evaluate to true or just be satisfiable
    * @throws SLTranslationException if the condition could not be parsed to a valid Term
    */
   public KeYWatchpointStopCondition(int hitCount, Proof proof, String condition, boolean enabled, boolean conditionEnabled, KeYJavaType containerType, boolean suspendOnTrue) throws SLTranslationException {
      super(hitCount, null, proof, enabled, conditionEnabled, -1, -1, containerType);
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
   protected boolean isInScopeForCondition(Node node) {
      return true;
   }
   
   @Override
   protected boolean conditionMet(RuleApp ruleApp, Proof proof, Node node)
         throws ProofInputException {
      if(suspendOnTrue){
         return super.conditionMet(ruleApp, proof, node);
      }else{
         Term negatedCondition = getProof().getServices().getTermBuilder().not(getCondition());
         //initialize values
         PosInOccurrence pio = ruleApp.posInOccurrence();
         Term term = pio.subTerm();
         term = TermBuilder.goBelowUpdates(term);
         IExecutionContext ec = JavaTools.getInnermostExecutionContext(term.javaBlock(), proof.getServices());
         //put values into map which have to be replaced
         if(ec!=null){
            getVariableNamingMap().put(getSelfVar(), ec.getRuntimeInstance());
         }
         //replace renamings etc.
         OpReplacer replacer = new OpReplacer(getVariableNamingMap(), getProof().getServices().getTermFactory());
         Term termForSideProof = replacer.replace(negatedCondition);
         //start side proof
         Term toProof = getProof().getServices().getTermBuilder().equals(getProof().getServices().getTermBuilder().tt(), termForSideProof);
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
   
   @Override
   protected boolean isBreakpointHit(SourceElement activeStatement, RuleApp ruleApp, Proof proof, Node node) throws ProofInputException {
      if(activeStatement != null && activeStatement.getStartPosition().getLine() != -1){
         return super.isBreakpointHit(activeStatement, ruleApp, proof, node);
      }
      return false;
   }
}
