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

import java.util.HashMap;
import java.util.HashSet;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.util.Pair;

/**
 * Rule that for closing a partner goal after a join
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
   private Pair<Term, Term> joinState = null;
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
   public CloseAfterJoin(Node joinNode, Pair<Term, Term> joinState, Term pc) {
      this.joinNode = joinNode;
      this.joinState = joinState;
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
   public ImmutableList<Goal> apply(Goal goal, Services services,
         RuleApp ruleApp) throws RuleAbortException {
      
      TermBuilder tb = services.getTermBuilder();
      
      ImmutableList<Goal> jpNewGoals = goal.split(2);
      
      Goal linkedGoal = jpNewGoals.head();
      linkedGoal.setBranchLabel("Joined with node " + joinNode.parent().serialNr());
      // Workaround: Disable linked goal to prevent strategies
      // from automatically working further on it.
      linkedGoal.setLinkedNode(joinNode);
      linkedGoal.setEnabled(false);
      
      Goal ruleIsWeakeningGoal = jpNewGoals.tail().head();
      ruleIsWeakeningGoal.setBranchLabel("Joined node is weakening");
            
      Term impForm = tb.imp(joinState.second, tb.apply(joinState.first, pc));
      for (QuantifiableVariable v : impForm.freeVars()) {
         impForm = tb.all(v, impForm);
      }
      ruleIsWeakeningGoal.addFormula(new SequentFormula(impForm), true, true);
      
      // Register partner nodes
      JOIN_NODE_TO_PARTNERS_MAP.get(joinNode).add(ruleIsWeakeningGoal.node());
      
      return jpNewGoals;
   }

   @Override
   public boolean isApplicable(Goal goal, PosInOccurrence pio) {
      return joinNode != null && joinState != null &&  pc != null;
   }

   @Override
   public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
      return new DefaultBuiltInRuleApp(this, pos);
   }
}
