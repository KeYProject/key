// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.LoopBodyTermLabel;
import de.uka.ilkd.key.logic.LoopInvariantNormalBehaviorTermLabel;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.SymbolicExecutionTermLabel;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;

/**
 * <p>
 * This class provides static methods to manage {@link ITermLabelWorker}s.
 * </p>
 * <p>
 * In case of taclet rules, an instance of this class is used to collect the
 * additional information which is required to compute the new term labels
 * in the {@link SyntacticalReplaceVisitor}.
 * </p>
 * @author Martin Hentschel
 * @see ITermLabelWorker
 * @see ITermLabel
 */
public final class TermLabelWorkerManagement {
   /**
    * The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten.
    */
   private PosInOccurrence applicationPosInOccurrence;
   
   /**
    * The {@link Rule} which is applied. 
    */
   private Rule rule;

   /**
    * The available {@link ITermLabelWorker}.
    */
   private ImmutableList<ITermLabelWorker> labelInstantiators;
   
   /**
    * Constructor.
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten. 
    * @param rule The {@link Rule} which is applied. 
    * @param labelInstantiators The available {@link ITermLabelWorker}.
    */
   public TermLabelWorkerManagement(PosInOccurrence applicationPosInOccurrence, 
                                          Rule rule, 
                                          ImmutableList<ITermLabelWorker> labelInstantiators) {
      this.applicationPosInOccurrence = applicationPosInOccurrence;
      this.rule = rule;
      this.labelInstantiators = labelInstantiators;
   }
   
   /**
    * Computes the {@link ITermLabel} to add to a new {@link Term} with
    * help of the {@link ITermLabelWorker}s available via {@link #labelInstantiators}.
    * @param tacletTerm The {@link Term} in the taclet which is responsible to instantiate the new {@link Term} or {@code null} in case of build in rules. 
    * @param newTermOp The new {@link Operator} of the {@link Term} to create.
    * @param newTermSubs The optional children of the {@link Term} to create.
    * @param newTermBoundVars The optional {@link QuantifiableVariable}s of the {@link Term} to create.
    * @param newTermJavaBlock The optional {@link JavaBlock} of the {@link Term} to create.
    * @return The {@link ITermLabel}s to add to the new {@link Term} which should be created.
    * @return The {@link ITermLabel}s to add to the new {@link Term} which should be created.
    */
   public ImmutableArray<ITermLabel> instantiateLabels(Term tacletTerm, 
                                                       Operator newTermOp, 
                                                       ImmutableArray<Term> newTermSubs, 
                                                       ImmutableArray<QuantifiableVariable> newTermBoundVars,
                                                       JavaBlock newTermJavaBlock) {
      return instantiateLabels(labelInstantiators, applicationPosInOccurrence, rule, null, tacletTerm, newTermOp, newTermSubs, newTermBoundVars, newTermJavaBlock);
   }
   
   /**
    * Computes the {@link ITermLabel} to add to a new {@link Term} with
    * help of the {@link ITermLabelWorker}s provided by {@link Proof} of the given {@link Services}.
    * @param services The {@link Services} which contains the {@link Proof} that provides the {@link ITermLabelWorker}s to use.
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten. 
    * @param rule The {@link Rule} which is applied. 
    * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
    * @param tacletTerm The {@link Term} in the taclet which is responsible to instantiate the new {@link Term} or {@code null} in case of build in rules. 
    * @param newTermOp The new {@link Operator} of the {@link Term} to create.
    * @param newTermSubs The optional children of the {@link Term} to create.
    * @param newTermBoundVars The optional {@link QuantifiableVariable}s of the {@link Term} to create.
    * @param newTermJavaBlock The optional {@link JavaBlock} of the {@link Term} to create.
    * @return The {@link ITermLabel}s to add to the new {@link Term} which should be created.
    */
   public static ImmutableArray<ITermLabel> instantiateLabels(Services services,
                                                              PosInOccurrence applicationPosInOccurrence,
                                                              Rule rule,
                                                              Goal goal,
                                                              Term tacletTerm, 
                                                              Operator newTermOp, 
                                                              ImmutableArray<Term> newTermSubs, 
                                                              ImmutableArray<QuantifiableVariable> newTermBoundVars,
                                                              JavaBlock newTermJavaBlock) {
      return instantiateLabels(getLabelInstantiators(services), applicationPosInOccurrence, rule, goal, tacletTerm, newTermOp, newTermSubs, newTermBoundVars, newTermJavaBlock);
   }
   
   /**
    * Returns all {@link ITermLabelWorker} contained in the {@link Proof} of the given {@link Services}.
    * @param services The {@link Services} which contains the proof to read {@link ITermLabelWorker}s from.
    * @return The {@link ITermLabelWorker}s contained in the {@link Proof} of the given {@link Services}.
    */
   public static ImmutableList<ITermLabelWorker> getLabelInstantiators(Services services) {
      return services.getProof().getSettings().getLabelSettings().getLabelInstantiators();
   }
   
   /**
    * Computes the {@link ITermLabel} to add to a new {@link Term} with
    * help of the given {@link ITermLabelWorker}s.
    * @param labelInstantiators The available {@link ITermLabelWorker}.
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten. 
    * @param rule The {@link Rule} which is applied. 
    * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
    * @param tacletTerm The {@link Term} in the taclet which is responsible to instantiate the new {@link Term} or {@code null} in case of build in rules. 
    * @param newTermOp The new {@link Operator} of the {@link Term} to create.
    * @param newTermSubs The optional children of the {@link Term} to create.
    * @param newTermBoundVars The optional {@link QuantifiableVariable}s of the {@link Term} to create.
    * @param newTermJavaBlock The optional {@link JavaBlock} of the {@link Term} to create.
    * @return The {@link ITermLabel}s to add to the new {@link Term} which should be created.
    */
   public static ImmutableArray<ITermLabel> instantiateLabels(ImmutableList<ITermLabelWorker> labelInstantiators,
                                                              PosInOccurrence applicationPosInOccurrence,
                                                              Rule rule,
                                                              Goal goal,
                                                              Term tacletTerm, 
                                                              Operator newTermOp, 
                                                              ImmutableArray<Term> newTermSubs, 
                                                              ImmutableArray<QuantifiableVariable> newTermBoundVars,
                                                              JavaBlock newTermJavaBlock) {
      List<ITermLabel> instantiatedLabels = new LinkedList<ITermLabel>();
      if (labelInstantiators != null) {
         for (ITermLabelWorker instantiator : labelInstantiators) {
            List<ITermLabel> labels = instantiator.instantiateLabels(tacletTerm, applicationPosInOccurrence, applicationPosInOccurrence != null ? applicationPosInOccurrence.subTerm() : null, rule, goal, newTermOp, newTermSubs, newTermBoundVars, newTermJavaBlock);
            if (labels != null) {
               instantiatedLabels.addAll(labels);
            }
         }
      }
      return new ImmutableArray<ITermLabel>(instantiatedLabels);
   }

   /**
    * <p>
    * Returns the {@link ITermLabelWorker} with the given name if available.
    * </p>
    * <p>
    * This method has to be extended to support new {@link ITermLabelWorker}s.
    * </p>
    * @param name The name of the requested {@link ITermLabelWorker}.
    * @return The {@link ITermLabelWorker} or {@code null} if not available.
    */
   public static ITermLabelWorker getInstantiator(String name) {
      if (SymbolicExecutionTermLabel.NAME.toString().equals(name)) {
         return SymbolicExecutionTermLabelInstantiator.INSTANCE;
      }
      else if (LoopBodyTermLabel.NAME.toString().equals(name)) {
         return LoopBodyTermLabelInstantiator.INSTANCE;
      }
      else if (LoopInvariantNormalBehaviorTermLabel.NAME.toString().equals(name)) {
         return LoopInvariantNormalBehaviorTermLabelInstantiator.INSTANCE;
      }
      else {
         return null;
      }
   }

   /**
    * Checks if the given {@link ITermLabelWorker} is used in the {@link Proof} of the given {@link Services}.
    * @param services The {@link Services} which provides the {@link Proof}.
    * @param instantiator The {@link ITermLabelWorker} to look for.
    * @return {@code true} {@link ITermLabelWorker} is available, {@code false} {@link ITermLabelWorker} is not available.
    */
   public static boolean hasInstantiator(Services services, ITermLabelWorker instantiator) {
      return getLabelInstantiators(services).contains(instantiator);
   }

   /**
    * Checks if at least one {@link ITermLabelWorker} is available in the {@link Proof} of the given {@link Services}.
    * @param services The {@link Services} which provides the {@link Proof}.
    * @return {@code true} at least one {@link ITermLabelWorker} is available, {@code false} if no {@link ITermLabelWorker}s are available.
    */
   public static boolean hasInstantiators(Services services) {
      return !getLabelInstantiators(services).isEmpty();
   }

   /**
    * 
    * @param tacletTerm
    * @param applicationPosInOccurrence
    * @param rule
    * @param goal
    */
   public static void updateLabels(Term tacletTerm, 
                                   PosInOccurrence applicationPosInOccurrence, 
                                   Rule rule, 
                                   Goal goal) {
      if (goal != null) {
         Sequent sequent = goal.sequent();
         ImmutableList<ITermLabelWorker> instantiators = getLabelInstantiators(goal.node().proof().getServices());
         updateLabels(tacletTerm, applicationPosInOccurrence, rule, goal, sequent.antecedent(), true, instantiators);
         updateLabels(tacletTerm, applicationPosInOccurrence, rule, goal, sequent.succedent(), false, instantiators);
      }
   }
   
   private static void updateLabels(Term tacletTerm, 
                                    PosInOccurrence applicationPosInOccurrence, 
                                    Rule rule, 
                                    Goal goal, 
                                    Semisequent semisequent, 
                                    boolean inAntec, 
                                    ImmutableList<ITermLabelWorker> instantiators) {
      for (SequentFormula sfa : semisequent) {
         Term updatedTerm = updateLabelsRecursive(tacletTerm, applicationPosInOccurrence, rule, goal, sfa.formula(), instantiators);
         goal.changeFormula(new SequentFormula(updatedTerm), 
                            new PosInOccurrence(sfa, PosInTerm.TOP_LEVEL, inAntec));
      }
   }

   private static Term updateLabelsRecursive(Term tacletTerm, 
                                             PosInOccurrence applicationPosInOccurrence, 
                                             Rule rule, 
                                             Goal goal, 
                                             Term term, 
                                             ImmutableList<ITermLabelWorker> labelInstantiators) {
      Term[] newSubs = new Term[term.arity()];
      for (int i = 0; i < newSubs.length; i++) {
         newSubs[i] = updateLabelsRecursive(tacletTerm, applicationPosInOccurrence, rule, goal, term.sub(i), labelInstantiators);
      }
      ImmutableArray<ITermLabel> newLabels = updateLabels(tacletTerm, applicationPosInOccurrence, rule, goal, term, labelInstantiators);
      return TermFactory.DEFAULT.createTerm(term.op(), newSubs, term.boundVars(), term.javaBlock(), newLabels);
   }

   private static ImmutableArray<ITermLabel> updateLabels(Term tacletTerm, 
                                                          PosInOccurrence applicationPosInOccurrence,
                                                          Rule rule, 
                                                          Goal goal,
                                                          Term term,
                                                          ImmutableList<ITermLabelWorker> labelInstantiators) {
      List<ITermLabel> updatedLabels = new LinkedList<ITermLabel>();
      if (labelInstantiators != null) {
         for (ITermLabelWorker instantiator : labelInstantiators) {
            List<ITermLabel> labels = instantiator.updateLabels(tacletTerm, applicationPosInOccurrence, term, rule, goal);
            if (labels != null) {
               updatedLabels.addAll(labels);
            }
         }
      }
      return new ImmutableArray<ITermLabel>(updatedLabels);
   }
}