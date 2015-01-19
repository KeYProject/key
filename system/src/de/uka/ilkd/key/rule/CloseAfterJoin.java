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

package de.uka.ilkd.key.rule;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofVisitor;
import de.uka.ilkd.key.rule.JoinRule.SymbolicExecutionState;

/**
 * Rule for closing a partner goal after a join
 * operation. It does so by adding a formula corresponding
 * to the new join node as an implicative premise to the
 * goal to close; if the join rule is sound, the such
 * manipulated goal should be closable by KeY. This particular
 * way for closing partner goals should ensure that proofs
 * can only be closed for sound join rules, i.e. rules
 * producing join states that are weakenings of the parent
 * states.
 * 
 * @author Dominic Scheurer
 */
public class CloseAfterJoin implements BuiltInRule {
   
   private static final String DISPLAY_NAME = "CloseAfterJoin";
   private static final Name RULE_NAME = new Name(DISPLAY_NAME);
   
   private Node joinNode = null;
   private SymbolicExecutionState joinState = null;
   private SymbolicExecutionState thisSEState = null;
   private Term pc = null;
   
   private static HashMap<Node, HashSet<Node>> JOIN_NODE_TO_PARTNERS_MAP =
         new HashMap<Node, HashSet<Node>>();
   
   /**
    * Returns the partner nodes for the given join node. Strictly
    * speaking, these are the direct children of the partner nodes
    * that were involved in joining.
    * 
    * @param joinNode Join node to get the partner nodes for.
    * @return The partner nodes for the given join node.
    */
   public static HashSet<Node> getPartnerNodesFor(Node joinNode) {
      return JOIN_NODE_TO_PARTNERS_MAP.get(joinNode);
   }
   
   @SuppressWarnings("unused")
   private CloseAfterJoin() {}
   
   /**
    * Creates a new CloseAfterJoin rule.
    * 
    * @param joinNode The node for the join goal. This is needed
    *    to add a reference to its parent in the partner goal at
    *    the place of this rule application.
    * @param joinState The join state; needed for adding an implicative
    *    premise ensuring the soundness of join rules.
    * @param pc The program counter (formula of the form U\<{...}\> PHI,
    *    where U is an update in normal form and PHI is a DL formula).
    */
   public CloseAfterJoin(
         Node joinNode,
         SymbolicExecutionState joinState,
         SymbolicExecutionState thisSEState,
         Term pc) {
      this.joinNode = joinNode;
      this.joinState = joinState;
      this.thisSEState = thisSEState;
      this.pc = pc;
      
      if (!JOIN_NODE_TO_PARTNERS_MAP.containsKey(joinNode)) {
         JOIN_NODE_TO_PARTNERS_MAP.put(joinNode, new HashSet<Node>());
      }
   }
   
   @Override
   public Name name() {
      return RULE_NAME;
   }

   @Override
   public String displayName() {
      return DISPLAY_NAME;
   }

   @Override
   public ImmutableList<Goal> apply(
         final Goal goal,
         final Services services,
         final RuleApp ruleApp) throws RuleAbortException {
      
      ImmutableList<Goal> jpNewGoals = goal.split(2);
      
      final Goal linkedGoal = jpNewGoals.head();
      linkedGoal.setBranchLabel("Joined with node " + joinNode.parent().serialNr());
      // Workaround: Disable linked goal to prevent strategies
      // from automatically working further on it.
      linkedGoal.node().setLinkedNode(joinNode);
      linkedGoal.setEnabled(false);
      
      // Add a listener to close this node if the associated join
      // node has also been closed, and to remove the mark as linked
      // node if the join node has been pruned.
      final Node joinNodeF = joinNode;
      services.getProof().addProofTreeListener(new ProofTreeAdapter() {
         @Override
         public void proofGoalsChanged(ProofTreeEvent e) {
            if (joinNodeF.isClosed()) {
               // The joined node has been closed; now also close this node.
               services.getProof().closeGoal(linkedGoal);
            }
         }
         
         @Override
         public void proofPruned(ProofTreeEvent e) {
            if (!proofContainsNode(e.getSource(), joinNodeF)) {
               // The joined node has been pruned; now mark this node
               // as not linked and set it to automatic again.
               linkedGoal.node().setLinkedNode(null);
               linkedGoal.setEnabled(true);
            }
         }
         
      });
      
      Goal ruleIsWeakeningGoal = jpNewGoals.tail().head();
      ruleIsWeakeningGoal.setBranchLabel("Joined node is weakening");
            
      Term isWeakeningForm = getSyntacticWeakeningFormula(services);
      // Delete previous sequents      
      JoinRule.clearSemisequent(ruleIsWeakeningGoal, true);
      JoinRule.clearSemisequent(ruleIsWeakeningGoal, false);
      ruleIsWeakeningGoal.addFormula(new SequentFormula(isWeakeningForm), false, true);
      
      // Register partner nodes
      JOIN_NODE_TO_PARTNERS_MAP.get(joinNode).add(linkedGoal.node());
      
      return jpNewGoals;
   }
   
   private Term getSyntacticWeakeningFormula(Services services) {
      TermBuilder tb = services.getTermBuilder();
      
      final LinkedHashSet<QuantifiableVariable> allQfableVariables =
            new LinkedHashSet<QuantifiableVariable>();
//      allVariables.addAll(JoinRule.getFreeQfableVariables(thisSEState.getSymbolicState()));
//      allVariables.addAll(JoinRule.getFreeQfableVariables(joinState.getSymbolicState()));
//      allVariables.addAll(JoinRule.getFreeQfableVariables(thisSEState.getPathCondition()));
//      allVariables.addAll(JoinRule.getFreeQfableVariables(joinState.getPathCondition()));
      allQfableVariables.addAll(toList(thisSEState.getSymbolicState().freeVars()));
      allQfableVariables.addAll(toList(joinState.getSymbolicState().freeVars()));
      allQfableVariables.addAll(toList(thisSEState.getPathCondition().freeVars()));
      allQfableVariables.addAll(toList(joinState.getPathCondition().freeVars()));
      
      final LinkedHashSet<LocationVariable> allLocs =
            new LinkedHashSet<LocationVariable>();
      allLocs.addAll(JoinRule.getUpdateLocations(thisSEState.getSymbolicState()));
      allLocs.addAll(JoinRule.getUpdateLocations(joinState.getSymbolicState()));
      allLocs.addAll(JoinRule.getTermLocations(thisSEState.getPathCondition()));
      allLocs.addAll(JoinRule.getTermLocations(joinState.getPathCondition()));
      
      final LinkedList<Term> qfdVarTerms = new LinkedList<Term>();
      final LinkedList<Term> origQfdVarTerms = new LinkedList<Term>();
      
      final LinkedList<QuantifiableVariable> allVariables =
            new LinkedList<QuantifiableVariable>();
      allVariables.addAll(allQfableVariables);
      
      // Collect sorts and create logical variables for
      // closing over program variables.
      final LinkedList<Sort> argSorts = new LinkedList<Sort>();
      for (QuantifiableVariable var : allQfableVariables) {
         argSorts.add(var.sort());
         qfdVarTerms.add(tb.var(var));
         origQfdVarTerms.add(tb.var(var));
      }
      for (LocationVariable var : allLocs) {
         argSorts.add(var.sort());

         final String varNamePrefix = "v";
         final String newName = tb.newName(varNamePrefix);
         final LogicVariable newVar =
               new LogicVariable(new Name(newName), var.sort());
         services.getNamespaces().variables().add(newVar);
         
         qfdVarTerms.add(tb.var(newVar));
         allVariables.add(newVar);
         origQfdVarTerms.add(tb.var(var));
      }
      
      // Create and register the new predicate symbol
      final Name predicateSymbName = new Name(tb.newName("P"));
      
      final Function predicateSymb =
            new Function(predicateSymbName, Sort.FORMULA, new ImmutableArray<Sort>(argSorts));
      
      services.getNamespaces().functions().add(predicateSymb);
      
      // Create the predicate term
      final Term predTerm = tb.func(predicateSymb, origQfdVarTerms.toArray(new Term[] {}));
      
      // Create the formula (C1 & {U1} P(...)) -> (C2 & {U2} P(...))
      Term result = tb.imp(
            tb.and(
                  thisSEState.getPathCondition(),
                  tb.apply(thisSEState.getSymbolicState(), predTerm)),
            tb.and(
                  joinState.getPathCondition(),
                  tb.apply(joinState.getSymbolicState(), predTerm)));
      
      // Bind the program variables
      LocationVariable[] allLocsArr = allLocs.toArray(new LocationVariable[] {});
      Term bindForm = tb.tt();
      for (int i = allQfableVariables.size(); i < qfdVarTerms.size(); i++) {
         bindForm = tb.and(
               tb.equals(
                     tb.var(allLocsArr[i - allQfableVariables.size()]),
                     qfdVarTerms.get(i)),
               bindForm);
      }
      
      result = tb.imp(bindForm, result);
      
      // Form the universal closure
      result = tb.all(allVariables, result);
      
      return result;
   }

   @Override
   public boolean isApplicable(Goal goal, PosInOccurrence pio) {
      return joinNode != null && joinState != null &&  pc != null;
   }

   @Override
   public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
      return new DefaultBuiltInRuleApp(this, pos);
   }
   
   /**
    * Checks if the given node is contained in the given proof.
    * 
    * @param proof Proof to search.
    * @param node Node to search for.
    * @return True iff node is contained in proof.
    */
   private static boolean proofContainsNode(Proof proof, Node node) {
      FindNodeVisitor visitor = new FindNodeVisitor(node);
      proof.breadthFirstSearch(proof.root(), visitor);
      return visitor.success();
   }
   
   /**
    * Visitor for finding a node in a proof.
    * 
    * @author Dominic Scheurer
    */
   private static class FindNodeVisitor implements ProofVisitor {
      private boolean found = false;
      private Node node = null;
      
      @SuppressWarnings("unused")
      private FindNodeVisitor() {}
      
      /**
       * @param node The node to find in the proof.
       */
      public FindNodeVisitor(Node node) {
         this.node = node;
      }
      
      /**
       * @return True iff the given node has been found.
       */
      public boolean success() {
         return found;
      }
      
      @Override
      public void visit(Proof proof, Node visitedNode) {
         if (visitedNode.equals(node)) {
            found = true;
         }
      }
   }
   
   /**
    * Converts an {@link ImmutableSet} of {@link QuantifiableVariable}s to
    * a {@link LinkedList}.
    * 
    * @param set Set to convert to {@link LinkedList}.
    * @return A {@link LinkedList} from the given set.
    */
   private static LinkedList<QuantifiableVariable> toList(
         ImmutableSet<QuantifiableVariable> set) {
      return new LinkedList<QuantifiableVariable>(
            Arrays.asList(
                  set.toArray(new QuantifiableVariable[] {})));
   }
}
