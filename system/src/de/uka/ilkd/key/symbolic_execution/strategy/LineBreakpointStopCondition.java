package de.uka.ilkd.key.symbolic_execution.strategy;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.gui.ApplyStrategy.IStopCondition;
import de.uka.ilkd.key.gui.ApplyStrategy.SingleRuleApplicationInfo;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.UndeclaredProgramVariableCollector;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.RenamingTable;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Node.NodeIterator;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.translation.KeYJMLParser;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.ProofStarter;

/**
 * This{@link LineBreakpointStopCondition} represents a line breakpoint and is responsible to tell the debugger to stop execution when the respective
 * breakpoint is reached.
 * 
 * @author Marco Drebing
 */


public class LineBreakpointStopCondition extends ExecutedSymbolicExecutionTreeNodesStopCondition {
   


   /**
    * The {@link IPath} of the class this {@link LineBreakpointStopCondition} is associated with.
    */
   private IPath classPath;


   /**
    * The line of the Breakpoint in the respective class.
    */
   private int lineNumber;
   
   /**
    * The HitCount of the Breakpoint (set by user).
    */
   private int hitCount;
   
   /**
    * Counter for how often the Breakpoint was hit.
    */
   private int hitted = 0;
   
   /**
    * The condition  for this Breakpoint (set by user).
    */
   private Term condition;
   
   /**
    * The flag if the Breakpoint is enabled.
    */
   private boolean enabled;
   
   private boolean conditionEnabled;


   private ProgramVariable selfVar;
   
   private IProgramMethod pm;
   
   private KeYEnvironment<?> environment;
   
   public LineBreakpointStopCondition(IPath classPath, int lineNumber, int hitCount, KeYEnvironment<?> environment, IProgramMethod pm, String condition, boolean enabled, boolean conditionEnabled) throws SLTranslationException {
      super();
      this. environment = environment;
      this.pm = pm;
      
      this.condition = conditionEnabled ? computeTermForCondition(condition):TermBuilder.DF.tt();
      this.classPath=classPath;
      this.lineNumber=lineNumber;
      this.hitCount=hitCount;
      this.enabled=enabled;
      this.conditionEnabled = conditionEnabled;
      
      
   }
   
   
   public LineBreakpointStopCondition(IPath classPath, int lineNumber, int hitCount, KeYEnvironment<?> environment, String condition, boolean enabled, boolean conditionEnabled) throws SLTranslationException {
      super();
      this. environment = environment;
      
    
      
      this.condition = conditionEnabled ? computeTermForCondition(condition):TermBuilder.DF.tt();
      this.classPath=classPath;
      this.lineNumber=lineNumber;
      this.hitCount=hitCount;
      this.enabled=enabled;
      
      
   }


   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isGoalAllowed(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser, long startTime, int countApplied, Goal goal) {
      
         
         
         if(goal!=null){
            Node node = goal.node();
            RuleApp ruleApp = goal.getRuleAppManager().peekNext();
               if (SymbolicExecutionUtil.isSymbolicExecutionTreeNode(node, ruleApp)) {
                  // Check if the result for the current node was already computed.
                  Boolean value = getGoalAllowedResultPerSetNode().get(node);
                  if (value == null) {
                     // Get the number of executed set nodes on the current goal
                     Integer executedNumberOfSetNodes = getExecutedNumberOfSetNodesPerGoal().get(goal);
                     if (executedNumberOfSetNodes == null) {
                        executedNumberOfSetNodes = Integer.valueOf(0);
                     }
                     // Check if limit of set nodes of the current goal is exceeded
                     if (executedNumberOfSetNodes.intValue() + 1 > getMaximalNumberOfSetNodesToExecutePerGoal()) {
                        getGoalAllowedResultPerSetNode().put(node, Boolean.FALSE);
                        return false; // Limit of set nodes of this goal exceeded
                     }
                     else {
                        SourceElement activeStatement = NodeInfo.computeActiveStatement(ruleApp);
                        if (activeStatement != null && activeStatement.getEndPosition().getLine() != -1) {
                           IPath path = new Path(activeStatement.getPositionInfo().getParentClass());
                           int line = activeStatement.getEndPosition().getLine();
                           if(shouldStopInLine(line, path)&&(!conditionEnabled||conditionMet(ruleApp, proof, node))){
                           // Increase number of set nodes on this goal and allow rule application
                              executedNumberOfSetNodes = Integer.valueOf(executedNumberOfSetNodes.intValue() + 1);
                              getExecutedNumberOfSetNodesPerGoal().put(goal, executedNumberOfSetNodes);
                              getGoalAllowedResultPerSetNode().put(node, Boolean.TRUE);
                           }
                        }
                        return true; 
                     }
                  }
                  else {
                     // Reuse already computed result.
                     return value.booleanValue();
                  }
               }
            
         }
      
      return true;
   }



   


   /**
    * Checks if the execution should stop in the given line for the given class.
    * 
    * @param line The current line of code, that the auto mode is evaluating
    * @param path The {@link IPath} of the Class, that contains the currently evaluated code 
    * @return true if a {@link JavaLineBreakpoint} is in the given line and the condition evaluates to true and the Hitcount is exceeded, false otherwise
    */
   private boolean shouldStopInLine(int line, IPath path) {
            if (lineNumber == line && classPath.equals(path)) {
               return hitcountExceeded()&&enabled;
               }
      return false;
   }

   /**
    * Checks if the Hitcount is exceeded for the given {@link JavaLineBreakpoint}.
    * If the Hitcount is not exceeded the hitted counter is incremented, otherwise its set to 0.
    * 
    * @return true if the Hitcount is exceeded or the {@link JavaLineBreakpoint} has no Hitcount.
    * @throws CoreException
    */
   private boolean hitcountExceeded(){
      if (!(hitCount == -1)) {
         if (hitCount == hitted + 1) {
            hitted=0;
            return true;
         }
         else {
           hitted++;
         }
      }
      else {
         return true;
      }
      return false;
   }
   
   private boolean conditionMet(RuleApp ruleApp, Proof proof, Node node){
      try {
         PosInOccurrence pio = ruleApp.posInOccurrence();
         Term term = pio.subTerm();
         term = TermBuilder.DF.goBelowUpdates(term);
         IExecutionContext ec = JavaTools.getInnermostExecutionContext(term.javaBlock(), proof.getServices());
         
         
         Map<SVSubstitute, SVSubstitute> map = new HashMap<SVSubstitute, SVSubstitute>();
         
         map.put(selfVar, ec.getRuntimeInstance());
         OpReplacer replacer = new OpReplacer(map);
         Term termForSideProof = replacer.replace(condition);

         
         Term toProof = TermBuilder.DF.equals(TermBuilder.DF.tt(), termForSideProof);
         Sequent sequent = SymbolicExecutionUtil.createSequentToProveWithNewSuccedent(node, ruleApp, toProof);

         ApplyStrategyInfo info = SymbolicExecutionUtil.startSideProof(proof, sequent, StrategyProperties.SPLITTING_DELAYED);
         
         return info.getProof().closed();
      }
      catch (ProofInputException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
      

      return true;
   }


   public Term getCondition() {
      return condition;
   }

   public void setCondition(String condition) throws SLTranslationException {
      this.condition = conditionEnabled? computeTermForCondition(condition) : TermBuilder.DF.tt();
   }

   public int getHitCount() {
      return hitCount;
   }

   public void setHitCount(int hitCount) {
      this.hitCount = hitCount;
   }
   
   public boolean isEnabled() {
      return enabled;
   }

   public void setEnabled(boolean enabled) {
      this.enabled = enabled;
   }
   
   public void setConditionEnabled(boolean conditionEnabled) {
      this.conditionEnabled = conditionEnabled;
   }
   
   public int getLineNumber() {
      return lineNumber;
   }


   public boolean isConditionEnabled() {
      return conditionEnabled;
   }
   
   
   public IPath getClassPath() {
      return classPath;
   }
   
   private Term computeTermForCondition(String condition) throws SLTranslationException {
      selfVar = new LocationVariable(new ProgramElementName(TermBuilder.DF.newName(environment.getServices(), "self")), pm.getContainerType(), null, false, false);
      ImmutableList<ProgramVariable> paramVars = ImmutableSLList.nil();
      for (ParameterDeclaration pd : pm.getParameters()) {
         for (VariableSpecification vs : pd.getVariables()) {
            ProgramVariable paramVar = new LocationVariable(new ProgramElementName(TermBuilder.DF.newName(environment.getServices(), vs.getName())), (KeYJavaType) vs.getType(), pm.getContainerType(), false, false);
            paramVars = paramVars.append(paramVar);
         }
      }
      

    
      
      // TODO: Add to paramVars previously declared local variables like in ProgramMethodSubseetPO
      

//            TermBuilder.DF.paramVars(environment.getServices(), pm, true);
      // TODO: create paramVars like selfVar
      PositionedString ps = new PositionedString(condition);
      KeYJMLParser parser = new KeYJMLParser(ps, 
                                             environment.getServices(), 
                                             pm.getContainerType(), 
                                             selfVar, 
                                             paramVars, 
                                             null, 
                                             null, 
                                             null);
      
      return parser.parseExpression();
   }

   protected final void register(ProgramVariable pv) {
      Namespace progVarNames = environment.getServices().getNamespaces().programVariables();
      if (pv != null && progVarNames.lookup(pv.name()) == null) {
          progVarNames.addSafely(pv);
      }
 }
   
}
