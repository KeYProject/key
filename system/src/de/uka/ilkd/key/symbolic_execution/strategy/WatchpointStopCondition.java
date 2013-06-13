package de.uka.ilkd.key.symbolic_execution.strategy;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.RenamingTable;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.VariableNamer;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.translation.KeYJMLParser;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

public class WatchpointStopCondition extends
      ExecutedSymbolicExecutionTreeNodesStopCondition {

   
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
   private String condition;
   
   /**
    * The flag if the Breakpoint is enabled.
    */
   private boolean enabled;

   /**
    * A {@link ProgramVariable} representing the instance the class KeY is working on
    */
   private ProgramVariable selfVar;

   /**
    * The {@link KeYEnvironment} the proof is running in
    */
   private KeYEnvironment<?> environment;
   
   /**
    * A {@link Map} mapping from relevant variables for the condition to their runtime equivalent in KeY
    */
   private Map<SVSubstitute, SVSubstitute> variableNamingMap;

   private Proof proof;
   
   private ImmutableList<ProgramVariable> varsForCondition;
   
   
   

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
   public WatchpointStopCondition(int hitCount, KeYEnvironment<?> environment, Proof proof, String condition, boolean enabled){
      super();
      variableNamingMap=new HashMap<SVSubstitute, SVSubstitute>();
      this. environment = environment;
      this.hitCount=hitCount;
      this.enabled=enabled;
      this.condition=condition;
      this.proof=proof;
      varsForCondition = ImmutableSLList.nil();
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
            putValuesFromGlobalVars(node);
            addRenamings(node);
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
                           try{
                              if(conditionMet(ruleApp, proof, node, computeTermForCondition(node, ruleApp))&&hitcountExceeded()){
                                 // Increase number of set nodes on this goal and allow rule application
                                    executedNumberOfSetNodes = Integer.valueOf(executedNumberOfSetNodes.intValue() + 1);
                                    getExecutedNumberOfSetNodesPerGoal().put(goal, executedNumberOfSetNodes);
                                    getGoalAllowedResultPerSetNode().put(node, Boolean.TRUE);
                                 }
                           }catch(ProofInputException e){
                              //TODO
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

   

   
   private void addRenamings(Node node) {
      ImmutableList<RenamingTable> renamingTables = node.getRenamingTable();
      if (renamingTables != null && renamingTables.size() > 0) {
         //iterate over renaming tables
         Iterator<RenamingTable> itr = renamingTables.iterator();
         while (itr.hasNext()) {
            RenamingTable renamingTable = itr.next();
            //iterate over renamings within table
            Iterator<?> renameItr = renamingTable.getHashMap().entrySet().iterator();
            while (renameItr.hasNext()) {
               Map.Entry<? extends SourceElement, ? extends SourceElement> entry = (Entry<? extends SourceElement, ? extends SourceElement>) renameItr.next();
               if (entry.getKey() instanceof LocationVariable) {
                  for(ProgramVariable varForCondition : varsForCondition){
                     if(varForCondition instanceof ProgramVariable){
                        if ((VariableNamer.getBasename(((LocationVariable) entry.getKey()).name())).equals(varForCondition.name())||((LocationVariable) entry.getKey()).name().equals(varForCondition.name())) {
                           variableNamingMap.put(varForCondition, entry.getValue());
                        }
                     }
                  }
               }
            }
         }
      }
      
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
   
   /**
    * Checks if the condition, that was given by the user, evaluates to true with the current of the proof
    * 
    * @param ruleApp the {@link RuleApp} to be executed next
    * @param proof the current {@link Proof}
    * @param node the current {@link Node}
    * @return true if the condition evaluates to true
    * @throws ProofInputException 
    */
   private boolean conditionMet(RuleApp ruleApp, Proof proof, Node node, Term condition) throws ProofInputException{
      if(condition==null){
         return false;
      }
      //initialize values
      PosInOccurrence pio = ruleApp.posInOccurrence();
      Term term = pio.subTerm();
      term = TermBuilder.DF.goBelowUpdates(term);
      IExecutionContext ec = JavaTools.getInnermostExecutionContext(term.javaBlock(), proof.getServices());
      //put values into map which have to be replaced
      variableNamingMap.put(selfVar, ec.getRuntimeInstance());
      //replace renamings etc.
      OpReplacer replacer = new OpReplacer(variableNamingMap);
      Term termForSideProof = replacer.replace(condition);
      //start side proof
      Term toProof = TermBuilder.DF.equals(TermBuilder.DF.tt(), termForSideProof);
      Sequent sequent = SymbolicExecutionUtil.createSequentToProveWithNewSuccedent(node, ruleApp, toProof);
      ApplyStrategyInfo info = SymbolicExecutionUtil.startSideProof(proof, sequent, StrategyProperties.SPLITTING_DELAYED);
      return info.getProof().closed();
   }

   /**
    * Computes the Term that can be evaluated, from the user given condition
    * 
    * @param condition the condition given by the user
    * @return the {@link Term} that represents the condition
    * @throws SLTranslationException if the Term could not be parsed
    */
   private Term computeTermForCondition(Node node, RuleApp ruleApp) throws SLTranslationException {
      //collect all variables needed to parse the condition
      //collect global variables
         PosInOccurrence pio = ruleApp.posInOccurrence();
         Term term = pio.subTerm();
         term = TermBuilder.DF.goBelowUpdates(term);
         MethodFrame mf = JavaTools.getInnermostMethodFrame(term.javaBlock(), proof.getServices());
      
      KeYJavaType kjt = mf.getProgramMethod().getContainerType();
      IProgramMethod pm = mf.getProgramMethod();
      ProgramVariableCollector variableCollector = new ProgramVariableCollector(pm.getBody(), environment.getServices());
      variableCollector.start();
      Set<LocationVariable> undeclaredVariables = variableCollector.result();
      for(LocationVariable locVar : undeclaredVariables){
         boolean found = false;
         for(ProgramVariable paramVar : varsForCondition){
            if(paramVar.toString().equals(locVar.toString())){
               SVSubstitute value = variableNamingMap.get(paramVar);
               variableNamingMap.remove(paramVar);
               variableNamingMap.put(locVar, value);
               varsForCondition = varsForCondition.removeFirst(paramVar);
               varsForCondition = varsForCondition.append(locVar);
               found = true;
               break;
            }
         }
         if(!found){
            varsForCondition = varsForCondition.append(locVar);
         }
      }
      //parse string
      PositionedString ps = new PositionedString(condition);
      KeYJMLParser parser = new KeYJMLParser(ps, 
                                             environment.getServices(), 
                                             kjt, 
                                             selfVar, 
                                             varsForCondition, 
                                             null, 
                                             null, 
                                             null);
      try{
         return parser.parseExpression();
         }
      catch(Exception e){
         return null;
      }
   }

   /**
    * put values in toKeep and variableNamingMap that can be found in the global variables of the node
    * 
    * @param varForCondition
    * @param node
    * @param inScope
    */
   private void putValuesFromGlobalVars(Node node) {
      for(ProgramVariable progVar : node.getGlobalProgVars()){
         for(ProgramVariable varForCondition : varsForCondition){
            if(varForCondition.name().equals(progVar.name())&&(variableNamingMap.get(varForCondition)==null||variableNamingMap.get(varForCondition).equals(varForCondition))){
               variableNamingMap.put(varForCondition, progVar);
            }
         }
      }
   }


   /**
    * Returns the condition of the associated Breakpoint.
    * @return the condition of the associated Breakpoint
    */
   public String getCondition() {
      return condition;
   }
   
   
   /**
    * Sets the condition to the Term that is parsed from the given String.
    * @param condition the String to be parsed
    * @throws SLTranslationException if the parsing failed
    */
   public void setCondition(String condition) throws SLTranslationException {
      this.condition = condition;
   }

   /**
    * Returns the hitCount of the associated Breakpoint.
    * @return the hitCount of the associated Breakpoint
    */
   public int getHitCount() {
      return hitCount;
   }
   
   /**
    * Set the hitCount to the new value
    * @param hitCount the new value
    */
   public void setHitCount(int hitCount) {
      this.hitCount = hitCount;
   }
   
   /**
    * Checks if the Breakpoint is enabled.
    * @return true if Breakpoint is enabled
    */
   public boolean isEnabled() {
      return enabled;
   }

   /**
    * Sets the new enabled value.
    * @param enabled the new value
    */
   public void setEnabled(boolean enabled) {
      this.enabled = enabled;
   }

}
