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
import de.uka.ilkd.key.rule.label.TermLabelPolicy;
import de.uka.ilkd.key.rule.label.TermLabelRefactoring;
import de.uka.ilkd.key.rule.label.TermLabelUpdate;
import de.uka.ilkd.key.util.LinkedHashMap;

/**
 * <p>
 * This class provides access to the functionality of term labels.
 * </p>
 * <p>
 * A {@link TermLabelManager} is associated to a {@link Profile} object using
 * {@link Profile#getTermLabelManager()}. It allows:
 * <ul>
 *    <li>To list all supported {@link TermLabel} {@link Name}s via {@link #getSupportedTermLabelNames()}.</li>
 *    <li>To instantiate a {@link TermLabel} via {@link #parseLabel(String, List)}.</li>
 *    <li>To compute the {@link TermLabel}s of a {@link Term} to be created via {@link #instantiateLabels(Services, PosInOccurrence, Term, Rule, Goal, Object, Term, Operator, ImmutableArray, ImmutableArray, JavaBlock)} during rule application.</li>
 *    <li>To refactor existing {@link Term}s during rule application via {@link #refactorLabels(Services, PosInOccurrence, Term, Rule, Goal, Term)}.</li>
 * </ul>
 * <p>
 * <p>
 * For more information about {@link TermLabel}s and how they are maintained
 * during prove read the documentation of interface {@link TermLabel}.
 * </p>
 * @author Mattias Ulbrich
 * @see TermLabel
 */
public class TermLabelManager {
   /**
    * {@link Map}s the {@link Name} of a {@link TermLabel} to its {@link TermLabelFactory}.
    */
   private final Map<Name, TermLabelFactory<?>> factoryMap = new LinkedHashMap<Name, TermLabelFactory<?>>();

   /**
    * {@link Map}s the {@link Name} of a {@link TermLabel} to its {@link TermLabelPolicy} applied on the application {@link Term}.
    */
   private final Map<Name, TermLabelPolicy> applicationTermPolicyMap = new LinkedHashMap<Name, TermLabelPolicy>();

   /**
    * {@link Map}s the {@link Name} of a {@link TermLabel} to its {@link TermLabelPolicy} applied on the modality {@link Term}.
    */
   private final Map<Name, TermLabelPolicy> modalityTermPolicyMap = new LinkedHashMap<Name, TermLabelPolicy>();

   /**
    * All available {@link TermLabelUpdate}s.
    */
   private ImmutableList<TermLabelUpdate> updates = ImmutableSLList.<TermLabelUpdate>nil();

   /**
    * All available {@link TermLabelRefactoring}s.
    */
   private ImmutableList<TermLabelRefactoring> refactorings = ImmutableSLList.<TermLabelRefactoring>nil();

   /**
    * The {@link Name}s of all supported {@link TermLabel}s.
    */
   private ImmutableList<Name> supportedTermLabelnames = ImmutableSLList.<Name>nil();

   /**
    * Constructor.
    * @param configurations The {@link TermLabelConfiguration} which defines how to support each {@link TermLabel}.
    */
   public TermLabelManager(ImmutableList<TermLabelConfiguration> configurations) {
      if (configurations != null) {
         for (TermLabelConfiguration conf : configurations) {
            supportedTermLabelnames = supportedTermLabelnames.prepend(conf.getTermLabelName());
            factoryMap.put(conf.getTermLabelName(), conf.getFactory());
            if (conf.getApplicationTermPolicies() != null) {
               for (TermLabelPolicy policy : conf.getApplicationTermPolicies()) {
                  applicationTermPolicyMap.put(conf.getTermLabelName(), policy);
               }
            }
            if (conf.getModalityTermPolicies() != null) {
               for (TermLabelPolicy policy : conf.getModalityTermPolicies()) {
                  modalityTermPolicyMap.put(conf.getTermLabelName(), policy);
               }
            }
            if (conf.getTermLabelUpdates() != null) {
               updates = updates.prepend(conf.getTermLabelUpdates()); 
            }
            if (conf.getTermLabelRefactorings() != null) {
               refactorings = refactorings.prepend(conf.getTermLabelRefactorings()); 
            }
         }
      }
   }
   
   /**
    * Returns the {@link TermLabelManager} defined by the {@link Profile} of the given {@link Services}.
    * @param services The {@link Services} which provides the {@link TermLabelManager}.
    * @return The {@link TermLabelManager}s or {@code null} if not available.
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
    * Returns the {@link Name}s of all supported {@link TermLabel}s.
    * @return The {@link Name}s of all supported {@link TermLabel}s.
    */
   public Collection<Name> getSupportedTermLabelNames() {
      return factoryMap.keySet();
   }

   /**
    * <p>
    * Get a term label for string parameters.
    * </p>
    * <p>
    * Parses the string arguments and returns the term label of name
    * <code>name</code> with the corresponding parameters.
    * </p>
    * <p>
    * The name must be associated with a {@link TermLabelFactory}. Otherwise a
    * {@link TermLabelException} is thrown to indicate that an unknown term
    * label kind has been asked for.
    * </p>
    * @param name The name of the term label, not <code>null</code>
    * @param args The arguments, not <code>null</code>, no entry <code>null</code>
    * @return term label of kind {@code name} with parameters as parsed.
    * @throws TermLabelException if name is not a registered label name or the arguments cannot be parsed.
    */
   public TermLabel parseLabel(String name, List<String> args) throws TermLabelException {
      TermLabelFactory<?> factory = factoryMap.get(new Name(name));
      if (factory == null) {
         throw new TermLabelException("No TermLabelFactory available for term label name \"" + name + "\".");
      }
      else {
         return factory.parseInstance(args);
      }
   }
   
   /**
    * <p>
    * Computes the {@link TermLabel} to add to a new {@link Term} while
    * a {@link Rule} is currently active. The labels of the new {@link Term}
    * are computed just before the term is created.
    * </p>
    * <p>
    * This method delegates the request to the {@link TermLabelManager}
    * of the given {@link Services} if possible. Otherwise no labels are returned.
    * </p>
    * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is applied right now.
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten. 
    * @param bestMatchTerm Optionally the best matching {@link Term} in the previous {@link Sequent} from which the new {@link Term} will be created. This might be a child or grandchild of the {@link Term} defined by the {@link PosInOccurrence}.
    * @param rule The {@link Rule} which is applied. 
    * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
    * @param hint An optional hint passed from the active rule to describe the term which should be created. 
    * @param tacletTerm The optional {@link Term} in the taclet which is responsible to instantiate the new {@link Term} for the new proof node or {@code null} in case of built in rules. 
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
                                                             Object hint,
                                                             Term tacletTerm, 
                                                             Operator newTermOp, 
                                                             ImmutableArray<Term> newTermSubs, 
                                                             ImmutableArray<QuantifiableVariable> newTermBoundVars,
                                                             JavaBlock newTermJavaBlock) {
      TermLabelManager manager = getTermLabelManager(services); 
      if (manager != null) {
         Term applicationTerm = applicationPosInOccurrence != null ? applicationPosInOccurrence.subTerm() : null;
         return manager.instantiateLabels(services, 
                                          applicationPosInOccurrence, 
                                          applicationTerm, 
                                          rule, 
                                          goal, 
                                          hint, 
                                          tacletTerm, 
                                          newTermOp, 
                                          newTermSubs, 
                                          newTermBoundVars, 
                                          newTermJavaBlock);
      }
      else {
         return new ImmutableArray<TermLabel>();
      }
   }

   /**
    * Computes the {@link TermLabel} to add to a new {@link Term} while
    * a {@link Rule} is currently active. The labels of the new {@link Term}
    * are computed just before the term is created in the following way:
    * <ol>
    *    <li>An empty result {@link List} is created.</li>
    *    <li>All labels from taclet term are added to the result {@link List}.</li>
    *    <li>Existing labels on application term are added to result {@link List} if {@link TermLabelPolicy} wants to keep it.</li>
    *    <li>Existing labels on modality term are added to result {@link List} if {@link TermLabelPolicy} wants to keep it.</li>
    *    <li>All {@link TermLabelUpdate} are asked to add or remove labels from result {@link List}</li>
    *    <li>Result {@link List} is returned.</li>
    * </ol>
    * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is applied right now.
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten. 
    * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the previous {@link Sequent}.
    * @param rule The {@link Rule} which is applied. 
    * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
    * @param hint An optional hint passed from the active rule to describe the term which should be created. 
    * @param tacletTerm The optional {@link Term} in the taclet which is responsible to instantiate the new {@link Term} for the new proof node or {@code null} in case of built in rules. 
    * @param newTermOp The new {@link Operator} of the {@link Term} to create.
    * @param newTermSubs The optional children of the {@link Term} to create.
    * @param newTermBoundVars The optional {@link QuantifiableVariable}s of the {@link Term} to create.
    * @param newTermJavaBlock The optional {@link JavaBlock} of the {@link Term} to create.
    * @return The {@link TermLabel}s to add to the new {@link Term} which should be created.
    */
   public ImmutableArray<TermLabel> instantiateLabels(final Services services,
                                                      final PosInOccurrence applicationPosInOccurrence, 
                                                      final Term applicationTerm,
                                                      final Rule rule, 
                                                      final Goal goal, 
                                                      final Object hint,
                                                      final Term tacletTerm, 
                                                      final Operator newTermOp, 
                                                      final ImmutableArray<Term> newTermSubs, 
                                                      final ImmutableArray<QuantifiableVariable> newTermBoundVars, 
                                                      final JavaBlock newTermJavaBlock) {
      // Compute modality term if required
      Term modalityTerm = applicationTerm != null && (!modalityTermPolicyMap.isEmpty() || !updates.isEmpty()) ?
                          TermBuilder.DF.goBelowUpdates(applicationTerm) :
                          null;
      // Instantiate empty result
      final List<TermLabel> newLabels = new LinkedList<TermLabel>();
      // Add labels from taclet
      if (tacletTerm != null) {
         for (TermLabel label : tacletTerm.getLabels()) {
            newLabels.add(label);
         }
      }
      if (applicationTerm != null) {
         // Re-add exiting application term labels based on application term policies.
         if (!applicationTermPolicyMap.isEmpty()) {
            for (TermLabel label : applicationTerm.getLabels()) {
               TermLabelPolicy policy = applicationTermPolicyMap.get(label.name());
               if (policy != null && policy.keepLabel(services, applicationPosInOccurrence, applicationTerm, rule, goal, hint, tacletTerm, newTermOp, newTermSubs, newTermBoundVars, newTermJavaBlock, label)) {
                  newLabels.add(label);
               }
            }
         }
         // Re-add exiting modality term labels based on symbolic execution term policies.
         if (!modalityTermPolicyMap.isEmpty()) {
            for (TermLabel label : modalityTerm.getLabels()) {
               TermLabelPolicy policy = modalityTermPolicyMap.get(label.name());
               if (policy != null && policy.keepLabel(services, applicationPosInOccurrence, modalityTerm, rule, goal, hint, tacletTerm, newTermOp, newTermSubs, newTermBoundVars, newTermJavaBlock, label)) {
                  newLabels.add(label);
               }
            }
         }
      }
      // Allow updater to remove and add labels
      for (TermLabelUpdate update : updates) {
         update.updateLabels(services, applicationPosInOccurrence, applicationTerm, modalityTerm, rule, goal, hint, tacletTerm, newTermOp, newTermSubs, newTermBoundVars, newTermJavaBlock, newLabels);
      }
      return new ImmutableArray<TermLabel>(newLabels);
   }
   
   /**
    * <p>
    * Refactors all labels in the complete {@link Sequent}. This is the last
    * step of each rule application.
    * </p>
    * <p>
    * This method delegates the request to the {@link TermLabelManager}
    * of the given {@link Services} if possible. Otherwise no labels are returned.
    * </p>
    * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is applied right now.
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten. 
    * @param rule The {@link Rule} which is applied. 
    * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
    * @param tacletTerm The optional taclet {@link Term}. 
    */
   public static void refactorLabels(Services services,
                                     PosInOccurrence applicationPosInOccurrence, 
                                     Rule rule, 
                                     Goal goal,
                                     Term tacletTerm) {
      TermLabelManager manager = getTermLabelManager(services);
      if (manager != null) {
         Term applicationTerm = applicationPosInOccurrence != null ? applicationPosInOccurrence.subTerm() : null;
         manager.refactorLabels(services, applicationPosInOccurrence, applicationTerm, rule, goal, tacletTerm);
      }
   }

   /**
    * <p>
    * Refactors all labels in the complete {@link Sequent}. This is the last
    * step of each rule application.
    * </p>
    * <p>
    * This method delegates the request to the {@link TermLabelManager}
    * of the given {@link Services} if possible. Otherwise no labels are returned.
    * </p>
    * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is applied right now.
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten. 
    * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the previous {@link Sequent}.
    * @param rule The {@link Rule} which is applied. 
    * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
    * @param tacletTerm The optional taclet {@link Term}. 
    */
   public void refactorLabels(Services services,
                              PosInOccurrence applicationPosInOccurrence,
                              Term applicationTerm,
                              Rule rule, 
                              Goal goal,
                              Term tacletTerm) {
      // Compute active refactorings
      ImmutableList<TermLabelRefactoring> activeRefactorings = ImmutableSLList.nil();
      for (TermLabelRefactoring refactoring : refactorings) {
         if (refactoring.isRefactoringRequired(services, applicationPosInOccurrence, applicationTerm, rule, goal, tacletTerm)) {
            activeRefactorings = activeRefactorings.prepend(refactoring);
         }
      }
      // Do refactoring only if required
      if (!activeRefactorings.isEmpty()) {
         Sequent sequent = goal.sequent();
         refactorLabels(services, applicationPosInOccurrence, applicationTerm, rule, goal, tacletTerm, sequent.antecedent(), true, activeRefactorings);
         refactorLabels(services, applicationPosInOccurrence, applicationTerm, rule, goal, tacletTerm, sequent.succedent(), false, activeRefactorings);
      }
   }
   
   /**
    * Performs a {@link TermLabel} refactoring on the given {@link Semisequent}.
    * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is applied right now.
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten. 
    * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the previous {@link Sequent}.
    * @param rule The {@link Rule} which is applied. 
    * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
    * @param tacletTerm The optional taclet {@link Term}. 
    * @param semisequent The {@link Semisequent} to refactor.
    * @param inAntec {@code true} antecedent, {@code false} succedent.
    * @param activeRefactorings The active {@link TermLabelRefactoring}s to execute.
    */
   protected void refactorLabels(Services services,
                                 PosInOccurrence applicationPosInOccurrence, 
                                 Term applicationTerm,
                                 Rule rule, 
                                 Goal goal, 
                                 Term tacletTerm, 
                                 Semisequent semisequent, 
                                 boolean inAntec,
                                 ImmutableList<TermLabelRefactoring> activeRefactorings) {
      for (SequentFormula sfa : semisequent) {
         Term updatedTerm = refactorLabelsRecursive(services, applicationPosInOccurrence, applicationTerm, rule, goal, tacletTerm, sfa.formula(), activeRefactorings);
         goal.changeFormula(new SequentFormula(updatedTerm), 
                            new PosInOccurrence(sfa, PosInTerm.TOP_LEVEL, inAntec));
      }
   }

   /**
    * Performs a {@link TermLabel} refactoring recursively on the given {@link Term}.
    * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is applied right now.
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten. 
    * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the previous {@link Sequent}.
    * @param rule The {@link Rule} which is applied. 
    * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
    * @param tacletTerm The optional taclet {@link Term}. 
    * @param term The {@link Term} to refactor.
    * @param activeRefactorings The active {@link TermLabelRefactoring}s to execute.
    * @return The refactored {@link Term} in which the {@link TermLabel}s may have changed.
    */
   protected Term refactorLabelsRecursive(Services services,
                                          PosInOccurrence applicationPosInOccurrence,
                                          Term applicationTerm,
                                          Rule rule, 
                                          Goal goal, 
                                          Term tacletTerm, 
                                          Term term,
                                          ImmutableList<TermLabelRefactoring> activeRefactorings) {
      Term[] newSubs = new Term[term.arity()];
      for (int i = 0; i < newSubs.length; i++) {
         newSubs[i] = refactorLabelsRecursive(services, applicationPosInOccurrence, applicationTerm, rule, goal, tacletTerm, term.sub(i), activeRefactorings);
      }
      ImmutableArray<TermLabel> newLabels = performRefactoring(services, applicationPosInOccurrence, applicationTerm, rule, goal, tacletTerm, term, activeRefactorings);
      return TermFactory.DEFAULT.createTerm(term.op(), newSubs, term.boundVars(), term.javaBlock(), newLabels);
   }

   /**
    * Computes the new labels as part of the refactoring for the given {@link Term}.
    * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is applied right now.
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten. 
    * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the previous {@link Sequent}.
    * @param rule The {@link Rule} which is applied. 
    * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
    * @param tacletTerm The optional taclet {@link Term}. 
    * @param term The {@link Term} to refactor.
    * @param activeRefactorings The active {@link TermLabelRefactoring}s to execute.
    * @return The new {@link TermLabel} which should be used for the given {@link Term}.
    */
   protected ImmutableArray<TermLabel> performRefactoring(Services services,
                                                          PosInOccurrence applicationPosInOccurrence,
                                                          Term applicationTerm,
                                                          Rule rule, 
                                                          Goal goal,
                                                          Term tacletTerm, 
                                                          Term term,
                                                          ImmutableList<TermLabelRefactoring> activeRefactorings) {
      // Create list with all old labels
      List<TermLabel> newLabels = new LinkedList<TermLabel>();
      for (TermLabel oldLabel : term.getLabels()) {
         newLabels.add(oldLabel);
      }
      // Give all TermLabelInstantiator instances the chance to remove or to add labels from/to the list 
      for (TermLabelRefactoring refactoring : activeRefactorings) {
         refactoring.refactoreLabels(services, applicationPosInOccurrence, applicationTerm, rule, goal, tacletTerm, term, newLabels);
      }
      return new ImmutableArray<TermLabel>(newLabels);
   }
   
   /**
    * Instances of this class are used to group everything which is required
    * to support one specific {@link TermLabel}.
    * @author Martin Hentschel
    */
   public static final class TermLabelConfiguration {
      /**
       * The {@link Name} of the supported {@link TermLabel}.
       */
      private final Name termLabelName;
      
      /**
       * The {@link TermLabelFactory} to use.
       */
      private final TermLabelFactory<?> factory;
      
      /**
       * The {@link TermLabelPolicy} instances applied on the application term.
       */
      private final ImmutableList<TermLabelPolicy> applicationTermPolicies;
      
      /**
       * The {@link TermLabelPolicy} instances applied on the modality term.
       */
      private final ImmutableList<TermLabelPolicy> modalityTermPolicies;
      
      /**
       * The {@link TermLabelUpdate} instances.
       */
      private final ImmutableList<TermLabelUpdate> termLabelUpdates;
      
      /**
       * The {@link TermLabelRefactoring} instances.
       */
      private final ImmutableList<TermLabelRefactoring> termLabelRefactorings;

      /**
       * Constructor.
       * @param termLabelName The {@link Name} of the supported {@link TermLabel}.
       * @param factory The {@link TermLabelFactory} to use.
       */
      public TermLabelConfiguration(Name termLabelName, TermLabelFactory<?> factory) {
         this(termLabelName, factory, null, null, null, null);
      }

      /**
       * Constructor.
       * @param termLabelName The {@link Name} of the supported {@link TermLabel}.
       * @param factory The {@link TermLabelFactory} to use.
       * @param applicationTermPolicies The {@link TermLabelPolicy} instances applied on the application term.
       * @param modalityTermPolicies The {@link TermLabelPolicy} instances applied on the modality term.
       * @param termLabelUpdates The {@link TermLabelUpdate} instances.
       * @param termLabelRefactorings The {@link TermLabelRefactoring} instances.
       */
      public TermLabelConfiguration(Name termLabelName, 
                                    TermLabelFactory<?> factory, 
                                    ImmutableList<TermLabelPolicy> applicationTermPolicies, 
                                    ImmutableList<TermLabelPolicy> modalityTermPolicies, 
                                    ImmutableList<TermLabelUpdate> termLabelUpdates,
                                    ImmutableList<TermLabelRefactoring> termLabelRefactorings) {
         assert termLabelName != null;
         assert factory != null;
         this.termLabelName = termLabelName;
         this.factory = factory;
         this.applicationTermPolicies = applicationTermPolicies;
         this.modalityTermPolicies = modalityTermPolicies;
         this.termLabelUpdates = termLabelUpdates;
         this.termLabelRefactorings = termLabelRefactorings;
      }

      /**
       * Returns the {@link Name} of the supported {@link TermLabel}.
       * @return The {@link Name} of the supported {@link TermLabel}.
       */
      public Name getTermLabelName() {
         return termLabelName;
      }

      /**
       * Returns the {@link TermLabelFactory} to use.
       * @return The {@link TermLabelFactory} to use.
       */
      public TermLabelFactory<?> getFactory() {
         return factory;
      }

      /**
       * Returns the {@link TermLabelPolicy} instances applied on the application term.
       * @return The {@link TermLabelPolicy} instances applied on the application term.
       */
      public ImmutableList<TermLabelPolicy> getApplicationTermPolicies() {
         return applicationTermPolicies;
      }

      /**
       * Returns the {@link TermLabelPolicy} instances applied on the modality term.
       * @return The {@link TermLabelPolicy} instances applied on the modality term.
       */
      public ImmutableList<TermLabelPolicy> getModalityTermPolicies() {
         return modalityTermPolicies;
      }

      /**
       * Returns the {@link TermLabelUpdate} instances.
       * @return The {@link TermLabelUpdate} instances.
       */
      public ImmutableList<TermLabelUpdate> getTermLabelUpdates() {
         return termLabelUpdates;
      }

      /**
       * Returns the {@link TermLabelRefactoring} instances.
       * @return The {@link TermLabelRefactoring} instances.
       */
      public ImmutableList<TermLabelRefactoring> getTermLabelRefactorings() {
         return termLabelRefactorings;
      }
   }
}
