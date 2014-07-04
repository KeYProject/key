// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.strategy.breakpoint;

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
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.StatementContainer;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
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
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.translation.KeYJMLParser;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.util.SideProofUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Adds the funtionality to breakpoints to evaluate conditions.
 * @author Martin Hentschel
 */
public abstract class AbstractConditionalBreakpoint extends AbstractHitCountBreakpoint {
   /**
    * The condition  for this Breakpoint (set by user).
    */
   private Term condition;
   
   /**
    * The flag if the the condition for the associated Breakpoint is enabled
    */
   private boolean conditionEnabled;

   /**
    * The condition of the associated breakpoint saved as a String
    */
   private String conditionString;
  
   /**
    * A list of {@link ProgramVariable}s containing all variables that were parsed and have to be possibly replaced during runtime.
    */
   private ImmutableList<ProgramVariable> varsForCondition;
   
   /**
    * The KeYJavaType of the container of the element associated with the breakpoint.
    */
   private KeYJavaType containerType;

   /**
    * A list of variables KeY has to hold to evaluate the condition
    */
   private Set<LocationVariable> toKeep;
   
   /**
    * A {@link Map} mapping from relevant variables for the condition to their runtime equivalent in KeY
    */
   private Map<SVSubstitute, SVSubstitute> variableNamingMap;
  
   /**
    * The list of parameter variables of the method that contains the associated breakpoint
    */
   private Set<LocationVariable> paramVars;

   /**
    * A {@link ProgramVariable} representing the instance the class KeY is working on
    */
   private ProgramVariable selfVar;
   
   /**
    * The {@link IProgramMethod} this Breakpoint lies within
    */
   private IProgramMethod pm;

   /**
    * Creates a new {@link AbstractConditionalBreakpoint}. Call setCondition immediately after calling the constructor!
    * @param hitCount the number of hits after which the execution should hold at this breakpoint
    * @param pm the {@link IProgramMethod} representing the Method which the Breakpoint is located at
    * @param proof the {@link Proof} that will be executed and should stop
    * @param enabled flag if the Breakpoint is enabled
    * @param conditionEnabled flag if the condition is enabled
    * @param methodStart the line the containing method of this breakpoint starts at
    * @param methodEnd the line the containing method of this breakpoint ends at
    * @param containerType the type of the element containing the breakpoint
    */
   public AbstractConditionalBreakpoint(int hitCount, IProgramMethod pm, Proof proof, boolean enabled, boolean conditionEnabled, int methodStart, int methodEnd, KeYJavaType containerType){
      super(hitCount, proof,enabled);
      this.setPm(pm);
      paramVars= new HashSet<LocationVariable>();
      setVariableNamingMap(new HashMap<SVSubstitute, SVSubstitute>());
      toKeep = new HashSet<LocationVariable>();
      this.containerType=containerType;
      this.conditionEnabled = conditionEnabled;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void updateState(int maxApplications, 
                          long timeout, 
                          Proof proof, 
                          IGoalChooser goalChooser, 
                          long startTime, 
                          int countApplied, 
                          Goal goal) {
      super.updateState(maxApplications, timeout, proof, goalChooser, startTime, countApplied, goal);
      if (goal != null) {
         Node node = goal.node();
         RuleApp ruleApp = goal.getRuleAppManager().peekNext();
         if (getVarsForCondition() != null && ruleApp != null && node != null) {
            refreshVarMaps(ruleApp, node);
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
         if(inScope&&varForCondition.name().equals(progVar.name())&&(getVariableNamingMap().get(varForCondition)==null||getVariableNamingMap().get(varForCondition).equals(varForCondition))){
            toKeep.add((LocationVariable) progVar);
            getVariableNamingMap().put(varForCondition, progVar);
         }
      }
   }

   /**
    * Returns a map containing the same entries as the variableNamingMap changes in one map do not effect the other map
    * @return the cloned map
    */
   private Map<SVSubstitute, SVSubstitute> getOldMap() {
      Map<SVSubstitute, SVSubstitute> oldMap = new HashMap<SVSubstitute, SVSubstitute>();
      Iterator<?> iter = getVariableNamingMap().entrySet().iterator();
      while(iter.hasNext()){
         Map.Entry<?, ?> oldEntry = (Entry<?, ?>) iter.next();
         if(oldEntry.getKey() instanceof SVSubstitute && oldEntry.getValue() instanceof SVSubstitute){
            oldMap.put((SVSubstitute)oldEntry.getKey(), (SVSubstitute)oldEntry.getValue());
         }
      }
      return oldMap;
   }

   /**
    * removes all stored parameters in to Keep when the ruleApp on the current node would induce a method return
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
    * @param varForCondition the variable that might be relevant for the condition
    * @param node the current
    * @param inScope the flag to determine if the current statement is in the scope of the breakpoint
    * @param oldMap the oldMap variableNamings
    */
   private void putValuesFromRenamings(ProgramVariable varForCondition, Node node, boolean inScope, Map<SVSubstitute, SVSubstitute> oldMap, RuleApp ruleApp) {
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
               Map.Entry<?, ?> entry = (Entry<?, ?>) renameItr.next();
               if (entry.getKey() instanceof LocationVariable && entry.getValue()instanceof SVSubstitute) {
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
                     getVariableNamingMap().put(varForCondition, (SVSubstitute) entry.getValue());
                     found = true;
                     break;
                  }
                  else if (inScope && ((LocationVariable) entry.getKey()).name().equals(varForCondition.name())) {
                     //found relevant renaming for local variable
                     if (oldMap.get(varForCondition) != entry.getValue()) {
                        //remove old value from toKeep
                        toKeep.remove((LocationVariable) oldMap.get(varForCondition));
                     }
                     //add new value
                     toKeep.add((LocationVariable) entry.getValue());
                     getVariableNamingMap().put(varForCondition, (SVSubstitute) entry.getValue());
                     found = true;
                     break;
                  }
               }
            }
         }
      }
   }


   /**
    * Modifies toKeep and variableNamingMap to hold the correct parameters after execution of the given ruleApp on the given node
    * @param ruleApp the applied rule app
    * @param nodethe current node
    */
   protected void refreshVarMaps(RuleApp ruleApp, Node node) {
      boolean inScope = isInScope(node);
      // collect old values
      Map<SVSubstitute, SVSubstitute> oldMap = getOldMap();
      // put values into map which have to be replaced
      for (ProgramVariable varForCondition : getVarsForCondition()) {
         // put global variables only done when a variable is instantiated by
         // KeY for the first time
         putValuesFromGlobalVars(varForCondition, node, inScope);
         // put renamings into map and tokeep remove no longer need vars from
         // tokeep
         putValuesFromRenamings(varForCondition, node, isInScopeForCondition(node), oldMap, ruleApp);
      }
      freeVariablesAfterReturn(node, ruleApp, inScope);
   }
   
   /**
    * Computes the Term that can be evaluated, from the user given condition
    * @param condition the condition given by the user
    * @return the {@link Term} that represents the condition
    * @throws SLTranslationException if the Term could not be parsed
    */
   private Term computeTermForCondition(String condition) throws SLTranslationException {
      if(condition==null){
         return getProof().getServices().getTermBuilder().tt();
      }
      //collect all variables needed to parse the condition
      setSelfVar(new LocationVariable(new ProgramElementName(getProof().getServices().getTermBuilder().newName("self")), containerType, null, false, false));
      ImmutableList<ProgramVariable> varsForCondition = ImmutableSLList.nil();
      if(getPm()!=null){
       //collect parameter variables
         for (ParameterDeclaration pd : getPm().getParameters()) {
            for (VariableSpecification vs : pd.getVariables()) {
               this.paramVars.add((LocationVariable) vs.getProgramVariable());
               varsForCondition = varsForCondition.append((ProgramVariable) vs.getProgramVariable());
            }
         }
         // Collect local variables
         StatementBlock result = getStatementBlock(getPm().getBody());
         ProgramVariableCollector variableCollector = new ProgramVariableCollector(result, getProof().getServices());
         variableCollector.start();
         Set<LocationVariable> undeclaredVariables = variableCollector.result();
         for (LocationVariable x : undeclaredVariables) {
            varsForCondition = saveAddVariable(x, varsForCondition);
         }
      }
      JavaInfo info = getProof().getServices().getJavaInfo();
      ImmutableList<KeYJavaType> kjts = info.getAllSupertypes(containerType);
      ImmutableList<ProgramVariable> globalVars = ImmutableSLList.nil();
      for(KeYJavaType kjtloc: kjts){
         if (kjtloc.getJavaType() instanceof TypeDeclaration) {
            ImmutableList<Field> fields = info.getAllFields((TypeDeclaration)kjtloc.getJavaType());
            for(Field field : fields){
               if((kjtloc.equals(containerType)||!field.isPrivate())&&!((LocationVariable) field.getProgramVariable()).isImplicit())
                  globalVars = globalVars.append((ProgramVariable) field.getProgramVariable());
            }
         }
      }
      varsForCondition = varsForCondition.append(globalVars);
      this.setVarsForCondition(varsForCondition);
      //parse string
      PositionedString ps = new PositionedString(condition);
      KeYJMLParser parser = new KeYJMLParser(ps, 
                                             getProof().getServices(), 
                                             containerType, 
                                             getSelfVar(), 
                                             varsForCondition, 
                                             null, 
                                             null, 
                                             null);
      
         return parser.parseExpression();
      
   }
   
   /**
    * Checks if the condition, that was given by the user, evaluates to true with the current of the proof
    * @param ruleApp the {@link RuleApp} to be executed next
    * @param proof the current {@link Proof}
    * @param node the current {@link Node}
    * @return true if the condition evaluates to true
    */
   protected boolean conditionMet(RuleApp ruleApp, Proof proof, Node node) {
      ApplyStrategyInfo info = null;
      try {
         //initialize values
         PosInOccurrence pio = ruleApp.posInOccurrence();
         Term term = pio.subTerm();
         getProof().getServices().getTermBuilder();
         term = TermBuilder.goBelowUpdates(term);
         IExecutionContext ec = JavaTools.getInnermostExecutionContext(term.javaBlock(), proof.getServices());
         //put values into map which have to be replaced
         if(ec!=null){
            getVariableNamingMap().put(getSelfVar(), ec.getRuntimeInstance());
         }
         //replace renamings etc.
         OpReplacer replacer = new OpReplacer(getVariableNamingMap(), getProof().getServices().getTermFactory());
         Term termForSideProof = replacer.replace(condition);
         //start side proof
         Term toProof = getProof().getServices().getTermBuilder().equals(getProof().getServices().getTermBuilder().tt(), termForSideProof);
         Sequent sequent = SymbolicExecutionUtil.createSequentToProveWithNewSuccedent(node, ruleApp, toProof);
         info = SideProofUtil.startSideProof(proof, 
                                             sequent, 
                                             StrategyProperties.METHOD_CONTRACT,
                                             StrategyProperties.LOOP_INVARIANT,
                                             StrategyProperties.QUERY_ON,
                                             StrategyProperties.SPLITTING_DELAYED,
                                             false);
         return info.getProof().closed();
      }
      catch (ProofInputException e) {
         return false;
      }
      finally {
         SideProofUtil.disposeOrStore("Breakpoint condition computation on node " + node.serialNr() + ".", info);
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isBreakpointHit(SourceElement activeStatement, RuleApp ruleApp, Proof proof, Node node) {
      return (!conditionEnabled || conditionMet(ruleApp, proof, node)) &&
             super.isBreakpointHit(activeStatement, ruleApp, proof, node);
   }

   /**
    * For a given {@link StatementContainer} this method computes the {@link StatementBlock} that contains all lines before the line the Breakpoint is at, including the line itself.
    * 
    * @param statementContainer the {@link StatementContainer} to build the block from
    * @return the {@link StatementBlock} representing the container without the line below the Breakpoint
    */
   protected abstract StatementBlock getStatementBlock(StatementContainer statementContainer);

   /**
    * Checks if the statement of a given {@link Node} is in the scope of this breakpoint.
    * 
    * @param node the {@link Node} to be checked
    * @return true if the node represents a statement in the scope of this breakpoint.
    */
   protected abstract boolean isInScope(Node node);

   /**
    * Checks if the statement of a given {@link Node} is in the scope of this breakpoint.
    * 
    * @param node the {@link Node} to be checked
    * @return true if the node represents a statement in the scope of this breakpoint.
    */
   protected abstract boolean isInScopeForCondition(Node node);
   
   private ImmutableList<ProgramVariable> saveAddVariable(LocationVariable x, ImmutableList<ProgramVariable> varsForCondition) {
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
    * Sets the new conditionEnabled value.
    * @param conditionEnabled the new value
    */
   public void setConditionEnabled(boolean conditionEnabled) {
      this.conditionEnabled = conditionEnabled;
   }

   /**
    * Returns the condition of the associated Breakpoint.
    * @return the condition of the associated Breakpoint
    */
   public Term getCondition() {
      return condition;
   }

   /**
    * Checks if the condition for the associated Breakpoint is enabled.
    * @param conditionEnabled true if the condition for the associated Breakpoint is enabled
    */
   public boolean isConditionEnabled() {
      return conditionEnabled;
   }
   
   /**
    * Sets the condition to the Term that is parsed from the given String.
    * @param condition the String to be parsed
    * @throws SLTranslationException if the parsing failed
    */
   public void setCondition(String condition) throws SLTranslationException {
      this.conditionString = condition;
      this.condition = conditionEnabled? computeTermForCondition(condition) : getProof().getServices().getTermBuilder().tt();
   }
   
   /**
    * Returns the condition represented as a String.
    * @return the condition represented as a String
    */
   public String getConditionString() {
      return conditionString;
   }
   
   /**
    * Returns the variables KeY should keep to evaluate the condition.
    * @return the variables KeY should keep to evaluate the condition
    */
   public Set<LocationVariable> getToKeep() {
      return toKeep;
   }

   /**
    * @return the variableNamingMap
    */
   public Map<SVSubstitute, SVSubstitute> getVariableNamingMap() {
      return variableNamingMap;
   }

   /**
    * @param variableNamingMap the variableNamingMap to set
    */
   public void setVariableNamingMap(Map<SVSubstitute, SVSubstitute> variableNamingMap) {
      this.variableNamingMap = variableNamingMap;
   }

   /**
    * @return the selfVar
    */
   public ProgramVariable getSelfVar() {
      return selfVar;
   }

   /**
    * @param selfVar the selfVar to set
    */
   public void setSelfVar(ProgramVariable selfVar) {
      this.selfVar = selfVar;
   }

   /**
    * @return the varsForCondition
    */
   public ImmutableList<ProgramVariable> getVarsForCondition() {
      return varsForCondition;
   }

   /**
    * @param varsForCondition the varsForCondition to set
    */
   public void setVarsForCondition(ImmutableList<ProgramVariable> varsForCondition) {
      this.varsForCondition = varsForCondition;
   }

   /**
    * @return the pm
    */
   public IProgramMethod getPm() {
      return pm;
   }

   /**
    * @param pm the pm to set
    */
   public void setPm(IProgramMethod pm) {
      this.pm = pm;
   }
}