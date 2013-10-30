package de.uka.ilkd.key.logic.label;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.label.TermLabelUpdater;
import de.uka.ilkd.key.rule.label.TermPolicy;
import de.uka.ilkd.key.util.LinkedHashMap;

/**
 * This class provides access to the functionality of term labels.
 * 
 * <p>
 * A {@link TermLabelManager} is associated to a {@link Profile} object using
 * {@link Profile#getTermLabelManager()}. It grants access to
 * <ul>
 * <li>The list of names of all registered term labels using
 * {@link #getSupportedLabelNames()}
 * <li>The global {@link TermLabelInstantiator} which is not associated to a
 * particular label.
 * <li>The term label repository using the string parsing function
 * {@link #parseLabel(String, List)}
 * <li>The term label repository using retrieval queries
 * {@link #getLabel(Name, List)} and {@link #getLabel(Name, Object...)}
 * </ul>
 * 
 * <p>
 * Instantiators are usually associated to term labels directly. The methods
 * {@link TermLabel#getInstantiator()} can be used to retrieve the associated
 * instantiator for a label. However, some instantiators do not belong to a
 * label but are <em>global</em>. They are always applied not only on matching
 * terms.
 * 
 * <p>
 * The term label manager is initialised by static methods in the class
 * {@link TermLabels}. They register {@link TermLabelFactory} instances and
 * global {@link TermLabelInstantiator} objects using
 * <ul>
 * <li>{@link #addFactory(TermLabelFactory)}
 * <li>{@link #addGlobalInstantiator(TermLabelInstantiator)}
 * </ul>
 * 
 * <p>
 * Please see information in {@link TermLabels} on how to introduce new label
 * types.
 * </p>
 * 
 * @see TermLabel
 * @see TermLabels
 * @see TermLabelInstantiator
 * 
 * @author Mattias Ulbrich
 */
public class TermLabelManager {

   /**
    * The map from label names to their factories.
    */
   private final Map<Name, TermLabelFactory<?>> factoryMap = new LinkedHashMap<Name, TermLabelFactory<?>>();

   private final Map<Name, TermPolicy> applicationTermPolicyMap = new LinkedHashMap<Name, TermPolicy>();

   private final Map<Name, TermPolicy> symbolicExecutionTermPolicyMap = new LinkedHashMap<Name, TermPolicy>();

   private ImmutableList<TermLabelUpdater> updater = ImmutableSLList.<TermLabelUpdater>nil();

   public TermLabelManager(ImmutableList<TermLabelConfiguration> configurations) {
      if (configurations != null) {
         for (TermLabelConfiguration conf : configurations) {
            factoryMap.put(conf.getTermLabelName(), conf.getFactory());
            if (conf.getApplicationTermPolicies() != null) {
               for (TermPolicy policy : conf.getApplicationTermPolicies()) {
                  applicationTermPolicyMap.put(conf.getTermLabelName(), policy);
               }
            }
            if (conf.getSymbolicExecutionTermPolicies() != null) {
               for (TermPolicy policy : conf.getSymbolicExecutionTermPolicies()) {
                  symbolicExecutionTermPolicyMap.put(conf.getTermLabelName(), policy);
               }
            }
            if (conf.getTermLabelUpdater() != null) {
               updater = updater.prepend(conf.getTermLabelUpdater()); 
            }
         }
      }
   }
   
   /**
    * Returns all {@link TermLabelInstantiator} contained in the {@link Proof} of the given {@link Services}.
    * @param services The {@link Services} which contains the proof to read {@link TermLabelInstantiator}s from.
    * @return The {@link TermLabelInstantiator}s contained in the {@link Proof} of the given {@link Services}.
    */
   public static TermLabelManager getTermLabelManager(Services services) {
      TermLabelManager result = null;
      if (services != null) {
         Profile profile = services.getProfile();
         if (profile != null) {
            result = profile.getTermLabelManager();
         }
      }
      return result;
   }

   /**
    * Gets the registered supported label names.
    * 
    * @return an unmodifiable collection of names
    */
   public Collection<Name> getSupportedLabelNames() {
      return factoryMap.keySet();
   }

   /**
    * Get a term label for string parameters.
    * 
    * Parses the string arguments and returns the term label of name
    * <code>name</code> with the corresponding parameters.
    * 
    * <p>
    * The name must be associated with a {@link TermLabelFactory}. Otherwise a
    * {@link TermLabelException} is thrown to indicate that an unknown term
    * label kind has been asked for.
    * 
    * @param name
    *           the name of the term label, not <code>null</code>
    * @param args
    *           the arguments, not <code>null</code>, no entry <code>null</code>
    * @return term label of kind {@code name} with parameters as parsed.
    * @throws TermLabelException
    *            if name is not a registered label name or the arguments cannot
    *            be parsed.
    */
   public TermLabel parseLabel(String name, List<String> args)
         throws TermLabelException {

      TermLabelFactory<?> factory = factoryMap.get(new Name(name));
      if (factory == null) {
         throw new TermLabelException("Unknown label name: " + name);
      }
      else {
         return factory.parseInstance(args);
      }
   }
   
   /**
    * Computes the {@link TermLabel} to add to a new {@link Term} with
    * help of the given {@link TermLabelInstantiator}s.
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
                                                             Term bestMatchTerm,
                                                             Rule rule,
                                                             Goal goal,
                                                              Term tacletTerm, 
                                                              Operator newTermOp, 
                                                              ImmutableArray<Term> newTermSubs, 
                                                              ImmutableArray<QuantifiableVariable> newTermBoundVars,
                                                              JavaBlock newTermJavaBlock) {
      TermLabelManager manager = getTermLabelManager(services); 
      if (manager != null) {
         return manager.instantiateLabels(applicationPosInOccurrence, bestMatchTerm, rule, goal, tacletTerm, newTermOp, newTermSubs, newTermBoundVars, newTermJavaBlock);
      }
      else {
         return new ImmutableArray<TermLabel>();
      }
   }

   public ImmutableArray<TermLabel> instantiateLabels(PosInOccurrence applicationPosInOccurrence, 
                                                      Term bestMatchTerm,
                                                      Rule rule, 
                                                      Goal goal, 
                                                      Term tacletTerm, 
                                                      Operator newTermOp, 
                                                      ImmutableArray<Term> newTermSubs, 
                                                      ImmutableArray<QuantifiableVariable> newTermBoundVars, 
                                                      JavaBlock newTermJavaBlock) {
      // Compute required terms
      Term applicationTerm = applicationPosInOccurrence != null ? applicationPosInOccurrence.subTerm() : null;
      if (bestMatchTerm == null) {
         bestMatchTerm = applicationTerm;
      }
      // Instantiate empty result
      List<TermLabel> instantiatedLabels = new LinkedList<TermLabel>();
      // Add labels from taclet
      if (tacletTerm != null) {
         for (TermLabel label : tacletTerm.getLabels()) {
            instantiatedLabels.add(label);
         }
      }
      if (bestMatchTerm != null) {
         // Re-add exiting application term labels based on application term policies.
         if (!applicationTermPolicyMap.isEmpty()) {
            for (TermLabel label : bestMatchTerm.getLabels()) {
               TermPolicy policy = applicationTermPolicyMap.get(label.name());
               if (policy != null && policy.keepLabel(tacletTerm, applicationPosInOccurrence, applicationTerm, bestMatchTerm, rule, goal, newTermOp, newTermSubs, newTermBoundVars, newTermJavaBlock)) {
                  instantiatedLabels.add(label);
               }
            }
         }
         // Re-add exiting application term labels based on symbolic execution term policies.
         if (!symbolicExecutionTermPolicyMap.isEmpty()) {
            Term modalityTerm = TermBuilder.DF.goBelowUpdates(bestMatchTerm);
            for (TermLabel label : modalityTerm.getLabels()) {
               TermPolicy policy = symbolicExecutionTermPolicyMap.get(label.name());
               if (policy != null && policy.keepLabel(tacletTerm, applicationPosInOccurrence, applicationTerm, modalityTerm, rule, goal, newTermOp, newTermSubs, newTermBoundVars, newTermJavaBlock)) {
                  instantiatedLabels.add(label);
               }
            }
         }
      }
      return new ImmutableArray<TermLabel>(instantiatedLabels);
   }
   


   public static void updateLabels(Services services,
                                   Term tacletTerm, 
                                   PosInOccurrence applicationPosInOccurrence, 
                                   Rule rule, 
                                   Goal goal) {
      TermLabelManager manager = getTermLabelManager(services);
      if (manager != null) {
         manager.updateLabels(tacletTerm, applicationPosInOccurrence, rule, goal);
      }
   }

   /**
    * 
    * @param tacletTerm
    * @param applicationPosInOccurrence
    * @param rule
    * @param goal
    */
   public void updateLabels(Term tacletTerm, 
                                   PosInOccurrence applicationPosInOccurrence, 
                                   Rule rule, 
                                   Goal goal) {
      // Compute active updaters
      ImmutableList<TermLabelUpdater> activeUpdaters = ImmutableSLList.nil();
      for (TermLabelUpdater up : updater) {
         if (up.isUpdateRequired(tacletTerm, applicationPosInOccurrence, rule, goal)) {
            activeUpdaters = activeUpdaters.prepend(up);
         }
      }
      // Do update only if required
      if (!activeUpdaters.isEmpty()) {
         Sequent sequent = goal.sequent();
         updateLabels(tacletTerm, applicationPosInOccurrence, rule, goal, sequent.antecedent(), true, activeUpdaters);
         updateLabels(tacletTerm, applicationPosInOccurrence, rule, goal, sequent.succedent(), false, activeUpdaters);
      }
   }
   
   private void updateLabels(Term tacletTerm, 
                                    PosInOccurrence applicationPosInOccurrence, 
                                    Rule rule, 
                                    Goal goal, 
                                    Semisequent semisequent, 
                                    boolean inAntec,
                                    ImmutableList<TermLabelUpdater> activeUpdaters) {
      for (SequentFormula sfa : semisequent) {
         Term updatedTerm = updateLabelsRecursive(tacletTerm, applicationPosInOccurrence, rule, goal, sfa.formula(), activeUpdaters);
         goal.changeFormula(new SequentFormula(updatedTerm), 
                            new PosInOccurrence(sfa, PosInTerm.TOP_LEVEL, inAntec));
      }
   }

   private Term updateLabelsRecursive(Term tacletTerm, 
                                             PosInOccurrence applicationPosInOccurrence, 
                                             Rule rule, 
                                             Goal goal, 
                                             Term term,
                                             ImmutableList<TermLabelUpdater> activeUpdaters) {
      Term[] newSubs = new Term[term.arity()];
      for (int i = 0; i < newSubs.length; i++) {
         newSubs[i] = updateLabelsRecursive(tacletTerm, applicationPosInOccurrence, rule, goal, term.sub(i), activeUpdaters);
      }
      ImmutableArray<TermLabel> newLabels = updateLabels(tacletTerm, applicationPosInOccurrence, rule, goal, term, activeUpdaters);
      return TermFactory.DEFAULT.createTerm(term.op(), newSubs, term.boundVars(), term.javaBlock(), newLabels);
   }

   private ImmutableArray<TermLabel> updateLabels(Term tacletTerm, 
                                                  PosInOccurrence applicationPosInOccurrence,
                                                  Rule rule, 
                                                  Goal goal,
                                                  Term term,
                                                  ImmutableList<TermLabelUpdater> activeUpdaters) {
      // Create list with all old labels
      List<TermLabel> newLabels = new LinkedList<TermLabel>();
      for (TermLabel oldLabel : term.getLabels()) {
         newLabels.add(oldLabel);
      }
      // Give all TermLabelInstantiator instances the chance to remove or to add labels from/to the list 
      for (TermLabelUpdater updater : activeUpdaters) {
         updater.updateLabels(tacletTerm, applicationPosInOccurrence, term, rule, goal, newLabels);
      }
      return new ImmutableArray<TermLabel>(newLabels);
   }
   
   
   public static final class TermLabelConfiguration {
      private Name termLabelName;
      private TermLabelFactory<?> factory;
      private ImmutableList<TermPolicy> applicationTermPolicies;
      private ImmutableList<TermPolicy> symbolicExecutionTermPolicies;
      private ImmutableList<TermLabelUpdater> termLabelUpdater;

      public TermLabelConfiguration(Name termLabelName, TermLabelFactory<?> factory) {
         this(termLabelName, factory, null, null, null);
      }

      public TermLabelConfiguration(Name termLabelName, 
                                    TermLabelFactory<?> factory, 
                                    ImmutableList<TermPolicy> applicationTermPolicies, 
                                    ImmutableList<TermPolicy> symbolicExecutionTermPolicies, 
                                    ImmutableList<TermLabelUpdater> termLabelUpdater) {
         assert termLabelName != null;
         assert factory != null;
         this.termLabelName = termLabelName;
         this.factory = factory;
         this.applicationTermPolicies = applicationTermPolicies;
         this.symbolicExecutionTermPolicies = symbolicExecutionTermPolicies;
         this.termLabelUpdater = termLabelUpdater;
      }

      public Name getTermLabelName() {
         return termLabelName;
      }

      public TermLabelFactory<?> getFactory() {
         return factory;
      }

      public ImmutableList<TermPolicy> getApplicationTermPolicies() {
         return applicationTermPolicies;
      }

      public ImmutableList<TermPolicy> getSymbolicExecutionTermPolicies() {
         return symbolicExecutionTermPolicies;
      }

      public ImmutableList<TermLabelUpdater> getTermLabelUpdater() {
         return termLabelUpdater;
      }
   }
}
