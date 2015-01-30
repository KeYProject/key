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

import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.*;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
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
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofVisitor;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils;
import de.uka.ilkd.key.util.joinrule.SymbolicExecutionState;

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
   private Services services = null;
   
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
    * @param thisSEState The SE state corresponding to this state.
    * @param pc The program counter (formula of the form U\<{...}\> PHI,
    *    where U is an update in normal form and PHI is a DL formula).
    */
   public CloseAfterJoin(
         Node joinNode,
         SymbolicExecutionState joinState,
         SymbolicExecutionState thisSEState,
         Term pc,
         Services services) {
      this.joinNode = joinNode;
      this.joinState = joinState;
      this.thisSEState = thisSEState;
      this.pc = pc;
      this.services = services;
      
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
      clearSemisequent(ruleIsWeakeningGoal, true);
      clearSemisequent(ruleIsWeakeningGoal, false);
      ruleIsWeakeningGoal.addFormula(new SequentFormula(isWeakeningForm), false, true);
      
      // Register partner nodes
      JOIN_NODE_TO_PARTNERS_MAP.get(joinNode).add(linkedGoal.node());
      
      return jpNewGoals;
   }
   
   /**
    * Constructs the actual syntactic weakening formula \phi(s1, s2)
    * expressing that s2 is a weakening of s1.
    * 
    * @param services The services object.
    * @return The syntactic weakening formula for this.joinState and
    *    this.thisSEState.
    */
   private Term getSyntacticWeakeningFormula(Services services) {
      TermBuilder tb = services.getTermBuilder();
      
      final LinkedHashSet<LocationVariable> allLocs =
            new LinkedHashSet<LocationVariable>();
      allLocs.addAll(getUpdateLeftSideLocations(thisSEState.getSymbolicState()));
      allLocs.addAll(getUpdateLeftSideLocations(joinState.getSymbolicState()));
      allLocs.addAll(getTermLocations(thisSEState.getPathCondition()));
      allLocs.addAll(getTermLocations(joinState.getPathCondition()));
      
      final LinkedList<Term> origQfdVarTerms = new LinkedList<Term>();
      
      // Collect sorts and create logical variables for
      // closing over program variables.
      final LinkedList<Sort> argSorts = new LinkedList<Sort>();
      for (LocationVariable var : allLocs) {
         argSorts.add(var.sort());
         origQfdVarTerms.add(tb.var(var));
      }
      
      // Create and register the new predicate symbol
      final Name predicateSymbName = new Name(tb.newName("P"));
      
      final Function predicateSymb =
            new Function(predicateSymbName, Sort.FORMULA, new ImmutableArray<Sort>(argSorts));
      
      services.getNamespaces().functions().add(predicateSymb);
      
      // Create the predicate term
      final Term predTerm = tb.func(predicateSymb, origQfdVarTerms.toArray(new Term[] {}));
      
      // Create the formula All-Cl(C2 -> {U2} P(...)) -> All-Cl(C1 -> {U1} P(...))
      Term result = tb.imp(
            allClosure(tb.imp(
                  joinState.getPathCondition(),
                  tb.apply(joinState.getSymbolicState(), predTerm))),
            allClosure(tb.imp(
                  thisSEState.getPathCondition(),
                  tb.apply(thisSEState.getSymbolicState(), predTerm))));
      
      return result;
   }
   
   /**
    * Universally closes all logical and location variables in
    * the given term. Before, all Skolem constants in the term
    * are replaced by fresh variables, where multiple occurrences
    * of the same constant are replaced by the same variable.
    * 
    * @param term Term to universally close.
    * @param services The services object.
    * @return A new term which is equivalent to the universal closure
    *    of the argument term, with Skolem constants having been replaced
    *    by fresh variables before.
    */
   private Term allClosure(final Term term) {
      return JoinRuleUtils.allClosure(
            substConstantsByFreshVars(
                  term, new HashMap<Function, LogicVariable>(), services),
            services);
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
}
