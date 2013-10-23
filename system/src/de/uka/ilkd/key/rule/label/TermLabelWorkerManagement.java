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

package de.uka.ilkd.key.rule.label;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabels;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;

/**
 * <p>
 * This class provides static methods to manage {@link TermLabelInstantiator}s.
 * </p>
 * <p>
 * In case of taclet rules, an instance of this class is used to collect the
 * additional information which is required to compute the new term labels
 * in the {@link SyntacticalReplaceVisitor}.
 * </p>
 * @author Martin Hentschel
 * @see TermLabelInstantiator
 * @see TermLabel
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
    * The available {@link TermLabelInstantiator}.
    */
   private TermLabelInstantiator globalLabelInstantiator;
   
   /**
    * Constructor.
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten. 
    * @param rule The {@link Rule} which is applied. 
    * @param globalLabelInstantiator The available global {@link TermLabelInstantiator}.
    */
   public TermLabelWorkerManagement(PosInOccurrence applicationPosInOccurrence, 
                                          Rule rule, 
                                          TermLabelInstantiator globalLabelInstantiator) {
      this.applicationPosInOccurrence = applicationPosInOccurrence;
      this.rule = rule;
      this.globalLabelInstantiator = globalLabelInstantiator;
   }
   
   /**
    * Computes the {@link TermLabel} to add to a new {@link Term} with
    * help of the {@link TermLabelInstantiator}s available via {@link #labelInstantiators}.
    * @param tacletTerm The {@link Term} in the taclet which is responsible to instantiate the new {@link Term} or {@code null} in case of build in rules. 
    * @param newTermOp The new {@link Operator} of the {@link Term} to create.
    * @param newTermSubs The optional children of the {@link Term} to create.
    * @param newTermBoundVars The optional {@link QuantifiableVariable}s of the {@link Term} to create.
    * @param newTermJavaBlock The optional {@link JavaBlock} of the {@link Term} to create.
    * @return The {@link TermLabel}s to add to the new {@link Term} which should be created.
    * @return The {@link TermLabel}s to add to the new {@link Term} which should be created.
    */
   public ImmutableArray<TermLabel> instantiateLabels(Term tacletTerm, 
                                                       Operator newTermOp, 
                                                       ImmutableArray<Term> newTermSubs, 
                                                       ImmutableArray<QuantifiableVariable> newTermBoundVars,
                                                       JavaBlock newTermJavaBlock) {
      return instantiateLabels(globalLabelInstantiator, applicationPosInOccurrence, rule, null, tacletTerm, newTermOp, newTermSubs, newTermBoundVars, newTermJavaBlock);
   }
   
   /**
    * Computes the {@link TermLabel} to add to a new {@link Term} with
    * help of the {@link TermLabelInstantiator}s provided by {@link Proof} of the given {@link Services}.
    * @param services The {@link Services} which contains the {@link Proof} that provides the {@link TermLabelInstantiator}s to use.
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten. 
    * @param rule The {@link Rule} which is applied. 
    * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
    * @param tacletTerm The {@link Term} in the taclet which is responsible to instantiate the new {@link Term} or {@code null} in case of build in rules. 
    * @param newTermOp The new {@link Operator} of the {@link Term} to create.
    * @param newTermSubs The optional children of the {@link Term} to create.
    * @param newTermBoundVars The optional {@link QuantifiableVariable}s of the {@link Term} to create.
    * @param newTermJavaBlock The optional {@link JavaBlock} of the {@link Term} to create.
    * @return The {@link TermLabel}s to add to the new {@link Term} which should be created.
    */
   public static ImmutableArray<TermLabel> instantiateLabels(Services services,
                                                              PosInOccurrence applicationPosInOccurrence,
                                                              Rule rule,
                                                              Goal goal,
                                                              Term tacletTerm, 
                                                              Operator newTermOp, 
                                                              ImmutableArray<Term> newTermSubs, 
                                                              ImmutableArray<QuantifiableVariable> newTermBoundVars,
                                                              JavaBlock newTermJavaBlock) {
      return instantiateLabels(getGlobalLabelInstantiator(services), applicationPosInOccurrence, rule, goal, tacletTerm, newTermOp, newTermSubs, newTermBoundVars, newTermJavaBlock);
   }
   
   /**
    * Returns the global {@link TermLabelInstantiator} contained in the {@link Proof} of the given {@link Services}.
    * @param services The {@link Services} which contains the proof to read {@link TermLabelInstantiator}s from.
    * @return The global {@link TermLabelInstantiator} contained in the {@link Proof} of the given {@link Services}.
    */
   public static TermLabelInstantiator getGlobalLabelInstantiator(Services services) {
       TermLabelInstantiator result = null;
       if (services != null) {
           Proof proof = services.getProof();
           if (proof != null) {
               ProofEnvironment env = proof.env();
               if (env != null) {
                   InitConfig initConfig = env.getInitConfig();
                   if (initConfig != null) {
                       Profile profile = initConfig.getProfile();
                       if (profile != null) {
                           TermLabelManager manager = profile.getTermLabelManager();
                           if(manager != null) {
                               result = manager.getGlobalInstantiator();
                           }
                       }
                   }
               }
           }
       }
       return result;
   }
   
   /**
    * Computes the {@link TermLabel} to add to a new {@link Term} with
    * help of the {@link TermLabelInstantiator}s of the terms and the global {@link TermLabelInstantiator}.
    * @param labelInstantiators The available global {@link TermLabelInstantiator}.
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten. 
    * @param rule The {@link Rule} which is applied. 
    * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
    * @param tacletTerm The {@link Term} in the taclet which is responsible to instantiate the new {@link Term} or {@code null} in case of build in rules. 
    * @param newTermOp The new {@link Operator} of the {@link Term} to create.
    * @param newTermSubs The optional children of the {@link Term} to create.
    * @param newTermBoundVars The optional {@link QuantifiableVariable}s of the {@link Term} to create.
    * @param newTermJavaBlock The optional {@link JavaBlock} of the {@link Term} to create.
    * @return The {@link TermLabel}s to add to the new {@link Term} which should be created.
    */
   public static ImmutableArray<TermLabel> instantiateLabels(
           TermLabelInstantiator globalInstantiator,
           PosInOccurrence applicationPosInOccurrence,
           Rule rule,
           Goal goal,
           Term tacletTerm, 
           Operator newTermOp, 
           ImmutableArray<Term> newTermSubs, 
           ImmutableArray<QuantifiableVariable> newTermBoundVars,
           JavaBlock newTermJavaBlock) {
       Term applicationTerm = applicationPosInOccurrence != null ? 
               applicationPosInOccurrence.subTerm() : null;

       List<TermLabelInstantiator> relevantInstantiators = new LinkedList<TermLabelInstantiator>();
       extractRelevantInstantiators(tacletTerm, relevantInstantiators);
       extractRelevantInstantiators(applicationTerm, relevantInstantiators);
       if(globalInstantiator != null) {
           relevantInstantiators.add(globalInstantiator);
       }

       List<TermLabel> instantiatedLabels = new LinkedList<TermLabel>();
       for (TermLabelInstantiator instantiator : relevantInstantiators) {
           List<TermLabel> labels = instantiator.instantiateLabels(tacletTerm, applicationPosInOccurrence, applicationTerm, rule, goal, newTermOp, newTermSubs, newTermBoundVars, newTermJavaBlock);
           assert labels != null : "Instantiators must not return null";
           instantiatedLabels.addAll(labels);
       }

       return new ImmutableArray<TermLabel>(instantiatedLabels);
   }

   private static void extractRelevantInstantiators(Term term,
           List<TermLabelInstantiator> relevantInstantiators) {
       if(term != null) {
           for (TermLabel label : term.getLabels()) {
               TermLabelInstantiator instantiator = label.getInstantiator();
               if(instantiator != null && !relevantInstantiators.contains(instantiator)) {
                   relevantInstantiators.add(instantiator);
               }
           }
       }
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
         TermLabelInstantiator instantiators = getGlobalLabelInstantiator(goal.node().proof().getServices());
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
                                    TermLabelInstantiator globalInstantiator) {
      for (SequentFormula sfa : semisequent) {
         Term updatedTerm = updateLabelsRecursive(tacletTerm, applicationPosInOccurrence, rule, goal, sfa.formula(), globalInstantiator);
         goal.changeFormula(new SequentFormula(updatedTerm), 
                            new PosInOccurrence(sfa, PosInTerm.TOP_LEVEL, inAntec));
      }
   }

   private static Term updateLabelsRecursive(Term tacletTerm, 
                                             PosInOccurrence applicationPosInOccurrence, 
                                             Rule rule, 
                                             Goal goal, 
                                             Term term, 
                                             TermLabelInstantiator globalInstantiator) {
      Term[] newSubs = new Term[term.arity()];
      for (int i = 0; i < newSubs.length; i++) {
         newSubs[i] = updateLabelsRecursive(tacletTerm, applicationPosInOccurrence, rule, goal, term.sub(i), globalInstantiator);
      }
      ImmutableArray<TermLabel> newLabels = updateLabels(tacletTerm, applicationPosInOccurrence, rule, goal, term, globalInstantiator);
      return TermFactory.DEFAULT.createTerm(term.op(), newSubs, term.boundVars(), term.javaBlock(), newLabels);
   }

   private static ImmutableArray<TermLabel> updateLabels(Term tacletTerm, 
                                                          PosInOccurrence applicationPosInOccurrence,
                                                          Rule rule, 
                                                          Goal goal,
                                                          Term term,
                                                          TermLabelInstantiator globalInstantiator) {
      // Create list with all old labels
      List<TermLabel> newLabels = new LinkedList<TermLabel>();
      for (TermLabel oldLabel : term.getLabels()) {
         newLabels.add(oldLabel);
      }

      // Give all ITermLabelWorker instances the chance to remove or to add labels from/to the list
      List<TermLabelInstantiator> relevantInstantiators = new LinkedList<TermLabelInstantiator>();
      extractRelevantInstantiators(tacletTerm, relevantInstantiators);
      extractRelevantInstantiators(term, relevantInstantiators);
      if(globalInstantiator != null) {
          relevantInstantiators.add(globalInstantiator);
      }

      for(TermLabelInstantiator instantiator : relevantInstantiators) {
          instantiator.updateLabels(tacletTerm, applicationPosInOccurrence, term, rule, goal, newLabels);
      }

      return new ImmutableArray<TermLabel>(newLabels);
   }
}