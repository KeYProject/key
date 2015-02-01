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

package de.uka.ilkd.key.symbolic_execution.rule;

import java.util.Deque;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.util.SideProofUtil;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;

/**
 * Provides the basic functionality of {@link BuiltInRule} which
 * computes something in a side proof.
 * @author Martin Hentschel
 */
public abstract class AbstractSideProofRule implements BuiltInRule {
   /**
    * <p>
    * Creates a constant which is used in the original {@link Proof} to
    * store the computed result in form of {@code QueryResult = ...}
    * </p>
    * <p>
    * The used name is registered in the {@link Namespace} of the {@link Services}.
    * </p>
    * @param services The {@link Services} to use-
    * @param sort The {@link Sort} to use.
    * @return The created constant.
    */
   protected Function createResultConstant(Services services, Sort sort) {
      String functionName = services.getTermBuilder().newName("QueryResult");
      Function function = new Function(new Name(functionName), sort);
      services.getNamespaces().functions().addSafely(function);
      return function;
   }
   
   /**
    * Creates the result {@link Function} used in a predicate to compute the result in the side proof.
    * @param services The {@link Services} to use.
    * @param sort The {@link Sort} to use.
    * @return The created result {@link Function}.
    */
   protected Function createResultFunction(Services services, Sort sort) {
      return new Function(new Name(services.getTermBuilder().newName("ResultPredicate")), Sort.FORMULA, sort);
   }
   
   /**
    * <p>
    * Starts the side proof and extracts the result {@link Term} and conditions.
    * </p>
    * <p>
    * New used names are automatically added to the {@link Namespace} of the {@link Services}.
    * </p>
    * @param services The {@link Services} to use.
    * @param goal The {@link Goal} on which this {@link BuiltInRule} should be applied on.
    * @param sideProofEnvironment The given {@link ProofEnvironment} of the side proof.
    * @param sequentToProve The {@link Sequent} to prove in a side proof.
    * @param newPredicate The {@link Function} which is used to compute the result.
    * @return The found result {@link Term} and the conditions.
    * @throws ProofInputException Occurred Exception.
    */
   protected List<Triple<Term, Set<Term>, Node>> computeResultsAndConditions(Services services, 
                                                                             Goal goal, 
                                                                             ProofEnvironment sideProofEnvironment,
                                                                             Sequent sequentToProve, 
                                                                             Function newPredicate) throws ProofInputException {
      return SideProofUtil.computeResultsAndConditions(services, 
                                                       goal.proof(), 
                                                       sideProofEnvironment,
                                                       sequentToProve, 
                                                       newPredicate, 
                                                       "Side proof rule on node " + goal.node().serialNr() + ".", 
                                                       StrategyProperties.METHOD_CONTRACT,
                                                       StrategyProperties.LOOP_INVARIANT,
                                                       StrategyProperties.QUERY_ON,
                                                       StrategyProperties.SPLITTING_DELAYED,
                                                       true);
   }
   
   /**
    * Replaces the {@link Term} defined by the given {@link PosInOccurrence}
    * with the given new {@link Term}.
    * @param pio The {@link PosInOccurrence} which defines the {@link Term} to replace.
    * @param newTerm The new {@link Term}.
    * @return The created {@link SequentFormula} in which the {@link Term} is replaced.
    */
   protected static SequentFormula replace(PosInOccurrence pio, Term newTerm, Services services) {
      // Iterate along the PosInOccurrence and collect the parents and indices
      Deque<Pair<Integer, Term>> indexAndParents = new LinkedList<Pair<Integer, Term>>();
      Term root = pio.constrainedFormula().formula();
      final PosInTerm pit = pio.posInTerm();
      for (int i = 0, sz=pit.depth(); i<sz; i++) { 
         int next = pit.getIndexAt(i);
         indexAndParents.addFirst(new Pair<Integer, Term>(Integer.valueOf(next), root));
         root = root.sub(next);
      }
      // Iterate over the collected parents and replace terms
      root = newTerm;
      for (Pair<Integer, Term> pair : indexAndParents) {
         Term parent = pair.second;
         Term[] newSubs = parent.subs().toArray(new Term[parent.subs().size()]);
         newSubs[pair.first] = root;
         root =  services.getTermFactory().createTerm(parent.op(), newSubs, parent.boundVars(), parent.javaBlock(), parent.getLabels());
      }
      return new SequentFormula(root);
   }
}