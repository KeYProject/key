package de.uka.ilkd.key.symbolic_execution.strategy;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Services.ITermProgramVariableCollectorFactory;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.StatementContainer;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.ProgramElementName;
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
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import de.uka.ilkd.key.proof.TermProgramVariableCollectorKeepUpdatesForBreakpointconditions;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.translation.KeYJMLParser;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

public abstract class AbstractBreakpointStopCondition extends
      ExecutedSymbolicExecutionTreeNodesStopCondition {

   


   /**
    * The path of the class this {@link LineBreakpointStopCondition} is associated with.
    */
   private String classPath;


   /**
    * The line of the Breakpoint in the respective class.
    */
   protected int lineNumber;
   
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
   protected Term condition;
   
   /**
    * The flag if the Breakpoint is enabled.
    */
   protected boolean enabled;
   
   /**
    * The flag if the the condition for the associated Breakpoint is enabled
    */
   protected boolean conditionEnabled;

   /**
    * A {@link ProgramVariable} representing the instance the class KeY is working on
    */
   protected ProgramVariable selfVar;
   
   /**
    * The {@link IProgramMethod} this Breakpoint lies within
    */
   protected IProgramMethod pm;

   /**
    * The {@link KeYEnvironment} the proof is running in
    */
   protected KeYEnvironment<?> environment;
  
   /**
    * A list of {@link ProgramVariable}s containing all variables that were parsed and have to be possibly replaced during runtime.
    */
   protected ImmutableList<ProgramVariable> varsForCondition;

   /**
    * The {@link ITermProgramVariableCollectorFactory} for others to use when collecting variables to dismiss.
    */
   private ITermProgramVariableCollectorFactory programVariableCollectorFactory;
   
   /**
    * The {@link CompoundStopCondition} containing all BreakpointStopConditions relevant for the current {@link KeYEnvironment}
    */
   private CompoundStopCondition parentCondition;
   
   /**
    * A {@link Map} mapping from relevant variables for the condition to their runtime equivalent in KeY
    */
   private Map<SVSubstitute, SVSubstitute> variableNamingMap;
   
   /**
    * The start of the method containing the associated Breakpoint
    */
   protected int methodStart;
  
   /**
    * The end of the method containing the associated Breakpoint
    */
   protected int methodEnd;

   /**
    * A list of variables KeY has to hold to evaluate the condition
    */
   private Set<LocationVariable> toKeep;
  
   /**
    * The list of parameter variables of the method that contains the associated breakpoint
    */
   protected Set<LocationVariable> paramVars;


   private Map<Integer, Boolean> hittedNodes;


   private String conditionString;


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
   public AbstractBreakpointStopCondition(String classPath, int lineNumber, int hitCount, KeYEnvironment<?> environment, IProgramMethod pm, Proof proof, CompoundStopCondition parentCondition, String condition, boolean enabled, boolean conditionEnabled, int methodStart, int methodEnd) throws SLTranslationException {
      super();
      variableNamingMap=new HashMap<SVSubstitute, SVSubstitute>();
      toKeep = new HashSet<LocationVariable>();
      paramVars= new HashSet<LocationVariable>();
      this. environment = environment;
      this.pm = pm;
      this.classPath=classPath;
      this.lineNumber=lineNumber;
      this.hitCount=hitCount;
      this.enabled=enabled;
      this.conditionEnabled = conditionEnabled;
      this.parentCondition=parentCondition;
      this.methodEnd=methodEnd;
      this.methodStart=methodStart;
      this.condition = conditionEnabled ? computeTermForCondition(condition):TermBuilder.DF.tt(); 
      this.conditionString = condition;
      createNewFactory();
      proof.getServices().setFactory(programVariableCollectorFactory);
      hittedNodes = new HashMap<Integer, Boolean>();
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
            if(varsForCondition!=null&&ruleApp!=null&&node!=null){
               refreshVarMaps(ruleApp, node);
            }
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
                           String path = activeStatement.getPositionInfo().getParentClass();
                           int line = activeStatement.getEndPosition().getLine();
                           try{
                              if(shouldStopInLine(line, path, node)&&(!conditionEnabled||conditionMet(ruleApp, proof, node))){
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

   

   
   /**
    * Modifies toKeep and variableNamingMap to hold the correct parameters after execution of the given ruleApp on the given node
    * 
    * @param ruleApp
    * @param node
    */
   protected void refreshVarMaps(RuleApp ruleApp, Node node) {
      boolean inScope = isInScope(node);
      // collect old values
      Map<SVSubstitute, SVSubstitute> oldMap = getOldMap();
      // put values into map which have to be replaced
      for (ProgramVariable varForCondition : varsForCondition) {
         // put global variables only done when a variable is instantiated by
         // KeY for the first time
         putValuesFromGlobalVars(varForCondition, node, inScope);
         // put renamings into map and tokeep remove no longer need vars from
         // tokeep
         putValuesFromRenamings(varForCondition, node, inScope, oldMap);
      }
      freeVariablesAfterReturn(node, ruleApp, inScope);
   }

   /**
    * Checks if the execution should stop in the given line for the given class.
    * 
    * @param line The current line of code, that the auto mode is evaluating
    * @param path The path of the Class, that contains the currently evaluated code 
    * @return true if a {@link JavaLineBreakpoint} is in the given line and the condition evaluates to true and the Hitcount is exceeded, false otherwise
    */
   protected boolean shouldStopInLine(int line, String path, Node node) {
            if (lineNumber == line && classPath.equals(path)) {
               return hitcountExceeded(node)&&enabled;
               }
      return false;
   }
   
   /**
    * Checks if the Hitcount is exceeded for the given {@link JavaLineBreakpoint}.
    * If the Hitcount is not exceeded the hitted counter is incremented, otherwise its set to 0.
    * 
    * @return true if the Hitcount is exceeded or the {@link JavaLineBreakpoint} has no Hitcount.
    */
   protected boolean hitcountExceeded(Node node){
      if (!(hitCount == -1)) {
         if(!hittedNodes.containsKey(node.serialNr())){
            if (hitCount == hitted + 1) {
               hitted=0;
               hittedNodes.put(node.serialNr(), Boolean.TRUE);
               return true;
            }
            else {
               hittedNodes.put(node.serialNr(), Boolean.FALSE);
               hitted++;
            }
         }else {
            return hittedNodes.get(node.serialNr());
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
   protected boolean conditionMet(RuleApp ruleApp, Proof proof, Node node) throws ProofInputException{
      //initialize values
      PosInOccurrence pio = ruleApp.posInOccurrence();
      Term term = pio.subTerm();
      term = TermBuilder.DF.goBelowUpdates(term);
      IExecutionContext ec = JavaTools.getInnermostExecutionContext(term.javaBlock(), proof.getServices());
      //put values into map which have to be replaced
      if(ec!=null){
         variableNamingMap.put(selfVar, ec.getRuntimeInstance());
      }
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
   private Term computeTermForCondition(String condition) throws SLTranslationException {
      if(condition==null){
         return TermBuilder.DF.tt();
      }
      //collect all variables needed to parse the condition
      selfVar = new LocationVariable(new ProgramElementName(TermBuilder.DF.newName(environment.getServices(), "self")), pm.getContainerType(), null, false, false);
      ImmutableList<ProgramVariable> varsForCondition = ImmutableSLList.nil();
      //collect parameter variables
      for (ParameterDeclaration pd : pm.getParameters()) {
         for (VariableSpecification vs : pd.getVariables()) {
            this.paramVars.add((LocationVariable) vs.getProgramVariable());
            varsForCondition = varsForCondition.append((ProgramVariable) vs.getProgramVariable());
         }
      }
      // Collect local variables
      StatementBlock result = getStatementBlock(pm.getBody());
      ProgramVariableCollector variableCollector = new ProgramVariableCollector(result, environment.getServices());
      variableCollector.start();
      Set<LocationVariable> undeclaredVariables = variableCollector.result();
      for (LocationVariable x : undeclaredVariables) {
         varsForCondition = saveAddVariable(x, varsForCondition);
      }
      JavaInfo info = environment.getServices().getJavaInfo();
      KeYJavaType kjt = pm.getContainerType();
      ImmutableList<KeYJavaType> kjts = info.getAllSupertypes(kjt);
      ImmutableList<ProgramVariable> globalVars = ImmutableSLList.nil();
      for(KeYJavaType kjtloc: kjts){
         ImmutableList<Field> fields = info.getAllFields((ClassDeclaration)kjtloc.getJavaType());
         for(Field field : fields){
            if((kjtloc.equals(kjt)||!field.isPrivate())&&!((LocationVariable) field.getProgramVariable()).isImplicit())
               globalVars = globalVars.append((ProgramVariable) field.getProgramVariable());
         }
      }
      varsForCondition = varsForCondition.append(globalVars);
      this.varsForCondition=varsForCondition;
      //parse string
      PositionedString ps = new PositionedString(condition);
      KeYJMLParser parser = new KeYJMLParser(ps, 
                                             environment.getServices(), 
                                             pm.getContainerType(), 
                                             selfVar, 
                                             varsForCondition, 
                                             null, 
                                             null, 
                                             null);
      
         return parser.parseExpression();
      
   }

   private ImmutableList<ProgramVariable> saveAddVariable(LocationVariable x,
         ImmutableList<ProgramVariable> varsForCondition) {
      boolean contains = false;
      for(ProgramVariable paramVar : varsForCondition){
         if(paramVar.toString().equals(x.toString())){
            contains = true;
            break;
         }
      }
      if(!contains&&!x.isMember()){
         varsForCondition = varsForCondition.append(x);
      }
      return varsForCondition;
   }

   /**
    * For a given {@link StatementContainer} this method computes the {@link StatementBlock} that contains all lines before the line the Breakpoint is at, including the line itself.
    * 
    * @param statementContainer the {@link StatementContainer} to build the block from
    * @return the {@link StatementBlock} representing the container without the line below the Breakpoint
    */
   protected abstract StatementBlock getStatementBlock(StatementContainer statementContainer);

   /**
    * removes all stored parameters in to Keep when the ruleApp on the current node would induce a method return
    * 
    * @param node
    * @param ruleApp
    * @param inScope
    */
   private void freeVariablesAfterReturn(Node node, RuleApp ruleApp,boolean inScope) {
      if(SymbolicExecutionUtil.isMethodReturnNode(node, ruleApp)&&inScope){
         toKeep.clear();
      }
   }

   /**
    * put relevant values from the current nodes renamings in toKeep and variableNamingMap
    * 
    * @param varForCondition
    * @param node
    * @param inScope
    * @param oldMap
    */
   private void putValuesFromRenamings(ProgramVariable varForCondition, Node node, boolean inScope, Map<SVSubstitute, SVSubstitute> oldMap) {
      // look for renamings KeY did
      boolean found = false;
      //get current renaming tables
      ImmutableList<RenamingTable> renamingTables = node.getRenamingTable();
      if (renamingTables != null && renamingTables.size() > 0) {
         //iterate over renaming tables
         Iterator<RenamingTable> itr = renamingTables.iterator();
         while (itr.hasNext() && !found) {
            RenamingTable renamingTable = itr.next();
            //iterate over renamings within table
            Iterator<?> renameItr = renamingTable.getHashMap().entrySet().iterator();
            while (renameItr.hasNext()) {
               Map.Entry<? extends SourceElement, ? extends SourceElement> entry = (Entry<? extends SourceElement, ? extends SourceElement>) renameItr.next();
               if (entry.getKey() instanceof LocationVariable) {
                  if ((VariableNamer.getBasename(((LocationVariable) entry
                        .getKey()).name())).equals(varForCondition.name())
                        && ((LocationVariable) entry.getKey()).name().toString().contains("#")
                        && paramVars.contains(varForCondition)) {
                     //found relevant renaming for a parameter variable
                     if (oldMap.get(varForCondition) != entry.getValue()) {
                      //remove old value from toKeep
                        toKeep.remove((LocationVariable) oldMap.get(varForCondition));
                     }
                     //add new value
                     toKeep.add((LocationVariable) entry.getValue());
                     variableNamingMap.put(varForCondition, entry.getValue());
                     found = true;
                     break;
                  }
                  else if (inScope&& ((LocationVariable) entry.getKey()).name().equals(varForCondition.name())) {
                     //found relevant renaming for local variable
                     if (oldMap.get(varForCondition) != entry.getValue()) {
                        //remove old value from toKeep
                        toKeep.remove((LocationVariable) oldMap.get(varForCondition));
                     }
                     //add new value
                     toKeep.add((LocationVariable) entry.getValue());
                     variableNamingMap.put(varForCondition, entry.getValue());
                     found = true;
                     break;
                  }
               }
            }
         }
      }
   }

   /**
    * put values in toKeep and variableNamingMap that can be found in the global variables of the node
    * 
    * @param varForCondition
    * @param node
    * @param inScope
    */
   private void putValuesFromGlobalVars(ProgramVariable varForCondition, Node node, boolean inScope) {
      for(ProgramVariable progVar : node.getGlobalProgVars()){
         if(inScope&&varForCondition.name().equals(progVar.name())&&(variableNamingMap.get(varForCondition)==null||variableNamingMap.get(varForCondition).equals(varForCondition))){
            toKeep.add((LocationVariable) progVar);
            variableNamingMap.put(varForCondition, progVar);
         }
      }
   }

   /**
    * Returns a map containing the same entries as the variableNamingMap changes in one map do not effect the other map
    * 
    * @return the cloned map
    */
   private Map<SVSubstitute, SVSubstitute> getOldMap() {
      Map<SVSubstitute, SVSubstitute> oldMap = new HashMap<SVSubstitute, SVSubstitute>();
      Iterator<?> iter = variableNamingMap.entrySet().iterator();
      while(iter.hasNext()){
         Map.Entry<SVSubstitute, SVSubstitute> oldEntry = (Entry<SVSubstitute, SVSubstitute>) iter.next();
         oldMap.put(oldEntry.getKey(), oldEntry.getValue());
      }
      return oldMap;
   }

   protected boolean isInScope(Node node) {
      Node checkNode = node;
      while (checkNode != null) {
         SourceElement activeStatement = NodeInfo.computeActiveStatement(checkNode.getAppliedRuleApp());
         if (activeStatement != null && activeStatement.getStartPosition().getLine() != -1) {
            if (activeStatement.getStartPosition().getLine() >= methodStart && activeStatement.getEndPosition().getLine() <= methodEnd) {
               return true;
            }
            break;
         }
         checkNode = checkNode.parent();
      }
      return false;
   }

   /**
    * creates a new factory that should be used by others afterwards
    */
   private void createNewFactory() {
      programVariableCollectorFactory = new ITermProgramVariableCollectorFactory() {
         @Override
         public TermProgramVariableCollector create(Services services) {
            TermProgramVariableCollectorKeepUpdatesForBreakpointconditions collector = new TermProgramVariableCollectorKeepUpdatesForBreakpointconditions(services, parentCondition);
            
              return collector;
         }
      };
   }

   /**
    * Returns the condition of the associated Breakpoint.
    * @return the condition of the associated Breakpoint
    */
   public Term getCondition() {
      return condition;
   }
   
   
   /**
    * Sets the condition to the Term that is parsed from the given String.
    * @param condition the String to be parsed
    * @throws SLTranslationException if the parsing failed
    */
   public void setCondition(String condition) throws SLTranslationException {
      this.conditionString = condition;
      this.condition = conditionEnabled? computeTermForCondition(condition) : TermBuilder.DF.tt();
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
      
   /**
    * Sets the new conditionEnabled value.
    * @param conditionEnabled the new value
    */
   public void setConditionEnabled(boolean conditionEnabled) {
      this.conditionEnabled = conditionEnabled;
   }
   
   /**
    * Returns the line number of the associated Breakpoint.
    * @return the line number of the associated Breakpoint
    */
   public int getLineNumber() {
      return lineNumber;
   }

   /**
    * Checks if the condition for the associated Breakpoint is enabled.
    * @param conditionEnabled true if the condition for the associated Breakpoint is enabled
    */
   public boolean isConditionEnabled() {
      return conditionEnabled;
   }
      
   /**
    * Returns the the path of the class the breakpoint is in.
    * @return the the path of the class the breakpoint is in
    */
   public String getClassPath() {
      return classPath;
   }
   
   /**
    * Returns the the variables KeY should keep to evaluate the condition.
    * @return the the variables KeY should keep to evaluate the condition
    */
   public Set<LocationVariable> getToKeep() {
      return toKeep;
   }

   public String getConditionString() {
      return conditionString;
   }
}
