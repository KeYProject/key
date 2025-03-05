/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.label;

import java.util.*;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.label.*;
import de.uka.ilkd.key.rule.label.ChildTermLabelPolicy;
import de.uka.ilkd.key.rule.label.TermLabelMerger;
import de.uka.ilkd.key.rule.label.TermLabelPolicy;
import de.uka.ilkd.key.rule.label.TermLabelRefactoring;
import de.uka.ilkd.key.rule.label.TermLabelRefactoring.RefactoringScope;
import de.uka.ilkd.key.util.LinkedHashMap;

import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.Pair;
import org.key_project.util.java.CollectionUtil;

import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;

/**
 * <p>
 * This class provides access to the functionality of term labels.
 * </p>
 * <p>
 * A {@link TermLabelManager} is associated to a {@link Profile} object using
 * {@link Profile#getTermLabelManager()}. It allows:
 * <ul>
 * <li>To list all supported {@link TermLabel} {@link Name}s via
 * {@link #getSupportedTermLabelNames()}.</li>
 * <li>To instantiate a {@link TermLabel} via {@link #parseLabel(String, List, TermServices)}.</li>
 * <li>To compute the {@link TermLabel}s of a {@link Term} to be created via
 * {@link #instantiateLabels(TermLabelState, Services, PosInOccurrence, Rule, RuleApp, Goal, Object, Term, Term)}
 * during rule application.</li>
 * <li>To refactor existing {@link Term}s during rule application via:
 * <ul>
 * <li>{@link #refactorGoal(TermLabelState, Services, PosInOccurrence, Rule, Goal, Object, Term)}:
 * The full sequent</li>
 * <li>{@link #refactorSequentFormula(TermLabelState, Services, Term, PosInOccurrence, Rule, Goal, Object, Term)}
 * : The sequent formula which contains the application term on which the rule is applied</li>
 * <li>{@link #refactorTerm(TermLabelState, Services, PosInOccurrence, Term, Rule, Goal, Object, Term)}
 * : The current term.</li>
 * </ul>
 * </li>
 * </ul>
 * <p>
 * <p>
 * For more information about {@link TermLabel}s and how they are maintained during prove read the
 * documentation of interface {@link TermLabel}.
 * </p>
 *
 * @author Mattias Ulbrich
 * @see TermLabel
 */
public class TermLabelManager {
    /**
     * {@link Map}s the {@link Name} of a {@link TermLabel} to its {@link TermLabelFactory}.
     */
    private final Map<Name, TermLabelFactory<?>> factoryMap =
        new LinkedHashMap<>();

    /**
     * {@link Map}s the {@link Name} of a {@link TermLabel} to its {@link TermLabelPolicy} applied
     * on the application {@link Term}.
     */
    private final Map<Name, TermLabelPolicy> applicationTermPolicyMap =
        new LinkedHashMap<>();

    /**
     * {@link Map}s the {@link Name} of a {@link TermLabel} to its {@link TermLabelPolicy} applied
     * on the modality {@link Term}.
     */
    private final Map<Name, TermLabelPolicy> modalityTermPolicyMap =
        new LinkedHashMap<>();

    /**
     * All rule specific direct {@link ChildTermLabelPolicy}s.
     */
    private final Map<Name, Map<Name, ChildTermLabelPolicy>> ruleSpecificDirectChildTermLabelPolicies =
        new LinkedHashMap<>();

    /**
     * All rule independent direct {@link ChildTermLabelPolicy}s.
     */
    private final Map<Name, ChildTermLabelPolicy> allRulesDirectChildTermLabelPolicies =
        new LinkedHashMap<>();

    /**
     * All rule specific child and grandchild {@link ChildTermLabelPolicy}s.
     */
    private final Map<Name, Map<Name, ChildTermLabelPolicy>> ruleSpecificChildAndGrandchildTermLabelPolicies =
        new LinkedHashMap<>();

    /**
     * All rule independent child and grandchild {@link ChildTermLabelPolicy}s.
     */
    private final Map<Name, ChildTermLabelPolicy> allRulesChildAndGrandchildTermLabelPolicies =
        new LinkedHashMap<>();

    /**
     * All rule independent {@link TermLabelUpdate}s.
     */
    private final Map<Name, ImmutableList<TermLabelUpdate>> ruleSpecificUpdates =
        new LinkedHashMap<>();

    /**
     * All rule independent {@link TermLabelUpdate}s.
     */
    private ImmutableList<TermLabelUpdate> allRulesUpdates = ImmutableSLList.nil();

    /**
     * All rule specific {@link TermLabelRefactoring}s.
     */
    private final Map<Name, ImmutableList<TermLabelRefactoring>> ruleSpecificRefactorings =
        new LinkedHashMap<>();

    /**
     * All rule independent {@link TermLabelRefactoring}s.
     */
    private ImmutableList<TermLabelRefactoring> allRulesRefactorings =
        ImmutableSLList.nil();

    /**
     * The {@link Name}s of all supported {@link TermLabel}s.
     */
    private ImmutableList<Name> supportedTermLabelnames = ImmutableSLList.nil();

    /**
     * {@link Map}s the {@link Name} of a {@link TermLabel} to its {@link TermLabelMerger}.
     */
    private final Map<Name, TermLabelMerger> mergerMap = new LinkedHashMap<>();

    /**
     * Constructor.
     *
     * @param configurations The {@link TermLabelConfiguration} which defines how to support each
     *        {@link TermLabel}.
     */
    public TermLabelManager(ImmutableList<TermLabelConfiguration> configurations) {
        if (configurations != null) {
            for (TermLabelConfiguration conf : configurations) {
                supportedTermLabelnames = supportedTermLabelnames.prepend(conf.getTermLabelName());
                factoryMap.put(conf.getTermLabelName(), conf.getFactory());
                analyzeTermPolicies(conf.getTermLabelName(), conf.getApplicationTermPolicies(),
                    applicationTermPolicyMap);
                analyzeTermPolicies(conf.getTermLabelName(), conf.getModalityTermPolicies(),
                    modalityTermPolicyMap);
                analyzeChildTermPolicies(conf.getTermLabelName(),
                    conf.getDirectChildTermLabelPolicies(), allRulesDirectChildTermLabelPolicies,
                    ruleSpecificDirectChildTermLabelPolicies);
                analyzeChildTermPolicies(conf.getTermLabelName(),
                    conf.getChildAndGrandchildTermLabelPolicies(),
                    allRulesChildAndGrandchildTermLabelPolicies,
                    ruleSpecificChildAndGrandchildTermLabelPolicies);
                analyzeUpdates(conf.getTermLabelUpdates());
                analyzeRefactorings(conf.getTermLabelRefactorings());
                analyzeMerger(conf.getTermLabelName(), conf.getTermLabelMerger());
            }
        }
    }

    /**
     * Analyzes the given {@link TermLabelMerger} and adds it to {@link #mergerMap}.
     *
     * @param termLabelName The name of the supported {@link TermLabel}.
     * @param termLabelMerger The {@link TermLabelMerger} to use.
     */
    private void analyzeMerger(Name termLabelName, TermLabelMerger termLabelMerger) {
        if (termLabelMerger != null) {
            mergerMap.put(termLabelName, termLabelMerger);
        }
    }

    /**
     * <p>
     * Analyzes the given {@link TermLabelPolicy} and adds it to the given policy {@link Map}.
     * </p>
     * <p>
     * This is a helper {@link Map} of {@link #TermLabelManager(ImmutableList)}.
     * </p>
     *
     * @param termLabelName The name of the supported {@link TermLabel}.
     * @param policies The {@link TermLabelPolicy} instances to analyze.
     * @param policyMap The policy {@link Map} to update.
     */
    private void analyzeTermPolicies(Name termLabelName, ImmutableList<TermLabelPolicy> policies,
            Map<Name, TermLabelPolicy> policyMap) {
        if (policies != null) {
            for (TermLabelPolicy policy : policies) {
                policyMap.put(termLabelName, policy);
            }
        }
    }

    /**
     * <p>
     * Analyzes the given {@link ChildTermLabelPolicy} and adds it to the given policy {@link Map}s.
     * </p>
     * <p>
     * This is a helper {@link Map} of {@link #TermLabelManager(ImmutableList)}.
     * </p>
     *
     * @param termLabelName The name of the supported {@link TermLabel}.
     * @param policies The {@link ChildTermLabelPolicy} instances to analyze.
     * @param allRulesPolicyMap The policy {@link Map} with all rules to update.
     * @param ruleSpecificPolicyMap The rule specific policy {@link Map} to update.
     */
    private void analyzeChildTermPolicies(Name termLabelName,
            ImmutableList<ChildTermLabelPolicy> policies,
            Map<Name, ChildTermLabelPolicy> allRulesPolicyMap,
            Map<Name, Map<Name, ChildTermLabelPolicy>> ruleSpecificPolicyMap) {
        if (policies != null) {
            for (ChildTermLabelPolicy policy : policies) {
                ImmutableList<Name> supportedRules = policy.getSupportedRuleNames();
                if (supportedRules == null || supportedRules.isEmpty()) {
                    allRulesPolicyMap.put(termLabelName, policy);
                } else {
                    for (Name rule : supportedRules) {
                        Map<Name, ChildTermLabelPolicy> ruleMap = ruleSpecificPolicyMap.get(rule);
                        if (ruleMap == null) {
                            ruleMap = new LinkedHashMap<>();
                            ruleSpecificPolicyMap.put(rule, ruleMap);
                        }
                        ruleMap.put(termLabelName, policy);
                    }
                }
            }
        }
    }

    /**
     * <p>
     * Analyzes the given {@link TermLabelUpdate} and updates {@link #allRulesUpdates} and
     * {@link #ruleSpecificUpdates}.
     * </p>
     * <p>
     * This is a helper {@link Map} of {@link #TermLabelManager(ImmutableList)}.
     * </p>
     *
     * @param updates The {@link TermLabelUpdate}s to analyze.
     */
    private void analyzeUpdates(ImmutableList<TermLabelUpdate> updates) {
        if (updates != null) {
            for (TermLabelUpdate update : updates) {
                ImmutableList<Name> supportedRules = update.getSupportedRuleNames();
                if (supportedRules == null || supportedRules.isEmpty()) {
                    allRulesUpdates = allRulesUpdates.prepend(update);
                } else {
                    for (Name rule : supportedRules) {
                        ImmutableList<TermLabelUpdate> ruleUpdates = ruleSpecificUpdates.get(rule);
                        if (ruleUpdates == null) {
                            ruleUpdates = ImmutableSLList.nil();
                        }
                        ruleUpdates = ruleUpdates.prepend(update);
                        ruleSpecificUpdates.put(rule, ruleUpdates);
                    }
                }
            }
        }
    }

    /**
     * <p>
     * Analyzes the given {@link TermLabelRefactoring} and updates {@link #allRulesRefactorings} and
     * {@link #ruleSpecificRefactorings}.
     * </p>
     * <p>
     * This is a helper {@link Map} of {@link #TermLabelManager(ImmutableList)}.
     * </p>
     * param updates The {@link TermLabelUpdate}s to analyze.
     */
    private void analyzeRefactorings(ImmutableList<TermLabelRefactoring> refactorings) {
        if (refactorings != null) {
            for (TermLabelRefactoring refactoring : refactorings) {
                ImmutableList<Name> supportedRules = refactoring.getSupportedRuleNames();
                if (supportedRules == null || supportedRules.isEmpty()) {
                    allRulesRefactorings = allRulesRefactorings.prepend(refactoring);
                } else {
                    for (Name rule : supportedRules) {
                        ImmutableList<TermLabelRefactoring> ruleRefactorings =
                            ruleSpecificRefactorings.get(rule);
                        if (ruleRefactorings == null) {
                            ruleRefactorings = ImmutableSLList.nil();
                        }
                        ruleRefactorings = ruleRefactorings.prepend(refactoring);
                        ruleSpecificRefactorings.put(rule, ruleRefactorings);
                    }
                }
            }
        }
    }

    /**
     * Returns the {@link TermLabelManager} defined by the {@link Profile} of the given
     * {@link Services}.
     *
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
     * Returns the {@link Name}s of the supported {@link TermLabel}s.
     *
     * @param services The {@link Services} used by the {@link Proof} on which the {@link Name}s of
     *        supported {@link TermLabel}s are requested.
     * @return The {@link Name}s of the supported {@link TermLabel}s.
     */
    public static ImmutableList<Name> getSupportedTermLabelNames(Services services) {
        TermLabelManager manager = getTermLabelManager(services);
        if (manager != null) {
            return manager.getSupportedTermLabelNames();
        } else {
            return ImmutableSLList.nil();
        }
    }

    /**
     * Returns the {@link Name}s of all supported {@link TermLabel}s.
     *
     * @return The {@link Name}s of all supported {@link TermLabel}s.
     */
    public ImmutableList<Name> getSupportedTermLabelNames() {
        return supportedTermLabelnames;
    }

    /**
     * <p>
     * Get a term label for string parameters.
     * </p>
     * <p>
     * Parses the string arguments and returns the term label of name <code>name</code> with the
     * corresponding parameters.
     * </p>
     * <p>
     * The name must be associated with a {@link TermLabelFactory}. Otherwise a
     * {@link TermLabelException} is thrown to indicate that an unknown term label kind has been
     * asked for.
     * </p>
     *
     * @param name The name of the term label, not <code>null</code>
     * @param args The arguments, not <code>null</code>, no entry <code>null</code>
     * @param services a non-<code>null</code> services object to look up symbols
     * @return term label of kind {@code name} with parameters as parsed.
     * @throws TermLabelException if name is not a registered label name or the arguments cannot be
     *         parsed.
     */
    public TermLabel parseLabel(String name, List<String> args, TermServices services)
            throws TermLabelException {
        TermLabelFactory<?> factory = factoryMap.get(new Name(name));
        if (factory == null) {
            throw new TermLabelException(
                "No TermLabelFactory available for term label name \"" + name + "\".");
        } else {
            return factory.parseInstance(args, services);
        }
    }

    /**
     * Computes the {@link TermLabel}s for the new {@link Term} via
     * {@link #instantiateLabels(TermLabelState, Services, PosInOccurrence, Term, Rule, RuleApp, Goal, Object, Term, Term)}
     * and refactors the labels below the new {@link Term} in addition via
     * {@link #refactorTerm(TermLabelState, Services, PosInOccurrence, Term, Goal, Object, Rule, Term)}.
     *
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param state The {@link TermLabelState} of the current rule application.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param rule The {@link Rule} which is applied.
     * @param ruleApp The {@link RuleApp} which is currently performed.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional {@link Term} in the taclet which is responsible to instantiate
     *        the new {@link Term} for the new proof node or {@code null} in case of built-in rules.
     * @param newTerm The new {@link Term} to update its labels.
     * @return The {@link Term} with updates labels.
     */
    public static Term label(Services services, TermLabelState state,
            PosInOccurrence applicationPosInOccurrence, Rule rule, RuleApp ruleApp, Goal goal,
            Object hint, Term tacletTerm, Term newTerm) {
        Term applicationTerm =
            applicationPosInOccurrence != null ? applicationPosInOccurrence.subTerm() : null;
        return label(services, state, applicationTerm, applicationPosInOccurrence, rule, ruleApp,
            goal, hint, tacletTerm, newTerm);
    }

    /**
     * Computes the {@link TermLabel}s for the new {@link Term} via
     * {@link #instantiateLabels(TermLabelState, Services, PosInOccurrence, Term, Rule, RuleApp, Goal, Object, Term, Term)}
     * and refactors the labels below the new {@link Term} in addition via
     * {@link #refactorTerm(TermLabelState, Services, PosInOccurrence, Term, Goal, Object, Rule, Term)}.
     *
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param state The {@link TermLabelState} of the current rule application.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param rule The {@link Rule} which is applied.
     * @param ruleApp The {@link RuleApp} which is currently performed.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional {@link Term} in the taclet which is responsible to instantiate
     *        the new {@link Term} for the new proof node or {@code null} in case of built-in rules.
     * @param newTerm The new {@link Term} to update its labels.
     * @return The {@link Term} with updates labels.
     */
    public static Term label(Services services, TermLabelState state, Term applicationTerm,
            PosInOccurrence applicationPosInOccurrence, Rule rule, RuleApp ruleApp, Goal goal,
            Object hint, Term tacletTerm, Term newTerm) {
        TermLabelManager manager = getTermLabelManager(services);
        if (manager != null) {
            return manager.label(state, services, applicationTerm, applicationPosInOccurrence, rule,
                ruleApp, goal, hint, tacletTerm, newTerm);
        } else {
            return newTerm;
        }
    }

    /**
     * Computes the {@link TermLabel}s for the new {@link Term} via
     * {@link #instantiateLabels(TermLabelState, Services, PosInOccurrence, Term, Rule, RuleApp, Goal, Object, Term, Term)}
     * and refactors the labels below the new {@link Term} in addition via
     * {@link #refactorTerm(TermLabelState, Services, PosInOccurrence, Term, Goal, Object, Rule, Term)}.
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param rule The {@link Rule} which is applied.
     * @param ruleApp The {@link RuleApp} which is currently performed.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional {@link Term} in the taclet which is responsible to instantiate
     *        the new {@link Term} for the new proof node or {@code null} in case of built-in rules.
     * @param newTerm The new {@link Term} to update its labels.
     * @return The {@link Term} with updates labels.
     */
    public Term label(TermLabelState state, Services services, Term applicationTerm,
            PosInOccurrence applicationPosInOccurrence, Rule rule, RuleApp ruleApp, Goal goal,
            Object hint, Term tacletTerm, Term newTerm) {
        ImmutableArray<TermLabel> newLabels = instantiateLabels(state, services, applicationTerm,
            applicationPosInOccurrence, rule, ruleApp, goal, hint, tacletTerm, newTerm);
        Term newlyLabeledTerm = services.getTermBuilder().addLabel(newTerm, newLabels);
        return refactorTerm(state, services, applicationPosInOccurrence, newlyLabeledTerm, goal,
            hint, rule, tacletTerm);
    }

    /**
     * <p>
     * Computes the {@link TermLabel} to add to a new {@link Term} while a {@link Rule} is currently
     * active. The labels of the new {@link Term} are computed just before the term is created.
     * </p>
     * <p>
     * This method delegates the request to the {@link TermLabelManager} of the given
     * {@link Services} if possible. Otherwise no labels are returned.
     * </p>
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param rule The {@link Rule} which is applied.
     * @param ruleApp The {@link RuleApp} which is currently performed.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional {@link Term} in the taclet which is responsible to instantiate
     *        the new {@link Term} for the new proof node or {@code null} in case of built in rules.
     * @param newTerm the template for the new {@link Term} to create
     * @return The {@link TermLabel}s to add to the new {@link Term} which should be created.
     */
    public static ImmutableArray<TermLabel> instantiateLabels(TermLabelState state,
            Services services, PosInOccurrence applicationPosInOccurrence, Rule rule,
            RuleApp ruleApp, Goal goal, Object hint, Term tacletTerm, Term newTerm) {
        Term applicationTerm =
            applicationPosInOccurrence != null ? applicationPosInOccurrence.subTerm() : null;
        return instantiateLabels(state, services, applicationTerm, applicationPosInOccurrence, rule,
            ruleApp, goal, hint, tacletTerm, newTerm);
    }

    /**
     * <p>
     * Computes the {@link TermLabel} to add to a new {@link Term} while a {@link Rule} is currently
     * active. The labels of the new {@link Term} are computed just before the term is created.
     * </p>
     * <p>
     * This method delegates the request to the {@link TermLabelManager} of the given
     * {@link Services} if possible. Otherwise no labels are returned.
     * </p>
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param rule The {@link Rule} which is applied.
     * @param ruleApp The {@link RuleApp} which is currently performed.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional {@link Term} in the taclet which is responsible to instantiate
     *        the new {@link Term} for the new proof node or {@code null} in case of built in rules.
     * @param newTerm the template for the new {@link Term} to create
     * @return The {@link TermLabel}s to add to the new {@link Term} which should be created.
     */
    public static ImmutableArray<TermLabel> instantiateLabels(TermLabelState state,
            Services services, Term applicationTerm, PosInOccurrence applicationPosInOccurrence,
            Rule rule, RuleApp ruleApp, Goal goal, Object hint, Term tacletTerm, Term newTerm) {
        TermLabelManager manager = getTermLabelManager(services);
        if (manager != null) {
            return manager.instantiateLabels(state, services, applicationPosInOccurrence,
                applicationTerm, rule, ruleApp, goal, hint, tacletTerm, newTerm);
        } else {
            return new ImmutableArray<>();
        }
    }


    /**
     * Do application term specific stuff.
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional {@link Term} in the taclet which is responsible to instantiate
     *        the new {@link Term} for the new proof node or {@code null} in case of built in rules.
     * @param newTerm the template for the new {@link Term} to create
     * @param newLabels The set accumulating the {@link TermLabel}s to add to the new {@link Term}
     *        which should be created.
     */
    private void addLabelsBasedOnApplicationTerm(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm, Term newTerm, Set<TermLabel> newLabels) {
        if (applicationTerm == null) {
            return;
        }
        // Re-add exiting application term labels based on application term policies.
        performTermLabelPolicies(state, services, applicationPosInOccurrence, applicationTerm, rule,
            goal, hint, tacletTerm, newTerm, applicationTermPolicyMap, newLabels);
        // Add labels from direct child term policies.
        Map<Name, ChildTermLabelPolicy> activeDirectChildPolicies =
            computeActiveChildPolicies(services, applicationPosInOccurrence, applicationTerm, rule,
                goal, hint, tacletTerm, newTerm, ruleSpecificDirectChildTermLabelPolicies,
                allRulesDirectChildTermLabelPolicies);
        if (!activeDirectChildPolicies.isEmpty()) {
            performDirectChildPolicies(services, applicationPosInOccurrence, applicationTerm, rule,
                goal, hint, tacletTerm, newTerm, activeDirectChildPolicies, newLabels);
        }

        // Add labels from child and grandchild term policies.
        Map<Name, ChildTermLabelPolicy> activeChildAndGrandchildPolicies =
            computeActiveChildPolicies(services, applicationPosInOccurrence, applicationTerm, rule,
                goal, hint, tacletTerm, newTerm, ruleSpecificChildAndGrandchildTermLabelPolicies,
                allRulesChildAndGrandchildTermLabelPolicies);
        if (!activeChildAndGrandchildPolicies.isEmpty()) {
            performChildAndGrandchildPolicies(services, applicationPosInOccurrence, applicationTerm,
                rule, goal, hint, tacletTerm, newTerm, activeChildAndGrandchildPolicies, newLabels);
        }
    }

    /**
     * Computes the {@link TermLabel} to add to a new {@link Term} while a {@link Rule} is currently
     * active. The labels of the new {@link Term} are computed just before the term is created in
     * the following way:
     * <ol>
     * <li>An empty result {@link List} is created.</li>
     * <li>All labels from taclet term are added to the result {@link List}.</li>
     * <li>Existing labels on application term are added to result {@link List} if
     * {@link TermLabelPolicy} wants to keep it.</li>
     * <li>Existing labels on modality term are added to result {@link List} if
     * {@link TermLabelPolicy} wants to keep it.</li>
     * <li>All {@link TermLabelUpdate} are asked to add or remove labels from result
     * {@link List}</li>
     * <li>Result {@link List} is returned.</li>
     * </ol>
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param rule The {@link Rule} which is applied.
     * @param ruleApp The {@link RuleApp} which is currently performed.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional {@link Term} in the taclet which is responsible to instantiate
     *        the new {@link Term} for the new proof node or {@code null} in case of built in rules.
     * @param newTerm the template for the new {@link Term} to create
     * @return The {@link TermLabel}s to add to the new {@link Term} which should be created.
     */
    public ImmutableArray<TermLabel> instantiateLabels(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule,
            RuleApp ruleApp, Goal goal, Object hint, Term tacletTerm, Term newTerm) {
        // Compute current rule specific updates
        ImmutableList<TermLabelUpdate> currentRuleSpecificUpdates =
            rule != null ? ruleSpecificUpdates.get(rule.name()) : null;
        // Compute modality term if required
        Term modalityTerm = applicationTerm != null && (!modalityTermPolicyMap.isEmpty()
                || !allRulesUpdates.isEmpty() || currentRuleSpecificUpdates != null)
                        ? TermBuilder.goBelowUpdates(applicationTerm)
                        : null;
        // Instantiate empty result
        Set<TermLabel> newLabels = new LinkedHashSet<>();
        // Add labels from taclet
        if (tacletTerm != null && tacletTerm.hasLabels()) {
            performTacletTerm(tacletTerm, newLabels);
        }
        addLabelsBasedOnApplicationTerm(state, services, applicationPosInOccurrence,
            applicationTerm, rule, goal, hint, tacletTerm, newTerm, newLabels);
        // Re-add exiting modality term labels based on symbolic execution term policies.
        if (modalityTerm != null) {
            performTermLabelPolicies(state, services, applicationPosInOccurrence, modalityTerm,
                rule, goal, hint, tacletTerm, newTerm, modalityTermPolicyMap, newLabels);
        }
        // Allow rule specific updater to remove and add labels
        if (currentRuleSpecificUpdates != null) {
            performUpdater(state, services, applicationPosInOccurrence, applicationTerm,
                modalityTerm, rule, ruleApp, hint, tacletTerm, newTerm, currentRuleSpecificUpdates,
                newLabels);
        }
        // Allow all rule updater to remove and add labels
        if (!allRulesUpdates.isEmpty()) {
            performUpdater(state, services, applicationPosInOccurrence, applicationTerm,
                modalityTerm, rule, ruleApp, hint, tacletTerm, newTerm, allRulesUpdates, newLabels);
        }
        // Return result
        return new ImmutableArray<>(newLabels.toArray(new TermLabel[0]));
    }

    /**
     * <p>
     * Performs the {@link TermLabel}s provided by the taclet {@link Term}.
     * </p>
     * <p>
     * This is a helper {@link Map} of
     * {@link #instantiateLabels(TermLabelState, Services, PosInOccurrence, Rule, RuleApp, Goal, Object, Term, Term)}
     * </p>
     *
     * @param tacletTerm The optional {@link Term} in the taclet which is responsible to instantiate
     *        the new {@link Term} for the new proof node or {@code null} in case of built-in rules.
     * @param newLabels The result {@link Set} with the {@link TermLabel}s of the new {@link Term}.
     */
    protected void performTacletTerm(Term tacletTerm, Set<TermLabel> newLabels) {
        for (TermLabel label : tacletTerm.getLabels()) {
            newLabels.add(label);
        }
    }

    /**
     * <p>
     * Performs the given {@link TermLabelPolicy} instances.
     * </p>
     * <p>
     * This is a helper method of
     * {@link #instantiateLabels(TermLabelState, Services, PosInOccurrence, Rule, RuleApp, Goal, Object, Term, Term)}
     * </p>
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional {@link Term} in the taclet which is responsible to instantiate
     *        the new {@link Term} for the new proof node or {@code null} in case of built in rules.
     * @param newTerm the template for the new {@link Term} to create
     * @param policies The {@link TermLabelPolicy} instances to perform.
     * @param newLabels The result {@link Set} with the {@link TermLabel}s of the new {@link Term}.
     */
    protected void performTermLabelPolicies(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm, Term newTerm, Map<Name, TermLabelPolicy> policies,
            Set<TermLabel> newLabels) {
        if (applicationTerm.hasLabels() && !policies.isEmpty()) {
            for (TermLabel label : applicationTerm.getLabels()) {
                performTermLabelPolicies(state, services, applicationPosInOccurrence,
                    applicationTerm, rule, goal, hint, tacletTerm, newTerm, policies, newLabels,
                    label);
            }
        }
    }

    /**
     * <p>
     * Performs the given {@link TermLabelPolicy} instances.
     * </p>
     * <p>
     * This is a helper method of
     * {@link #performTermLabelPolicies(TermLabelState, Services, PosInOccurrence, Term, Rule, Goal, Object, Term, Term, Map, Set)}
     * </p>
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional {@link Term} in the taclet which is responsible to instantiate
     *        the new {@link Term} for the new proof node or {@code null} in case of built in rules.
     * @param newTerm the template for the new {@link Term} to create
     * @param policies The {@link TermLabelPolicy} instances to perform.
     * @param newLabels The result {@link Set} with the {@link TermLabel}s of the new {@link Term}.
     * @param label The current {@link TermLabel} to ask its {@link TermLabelPolicy}.
     */
    protected void performTermLabelPolicies(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm, Term newTerm, Map<Name, TermLabelPolicy> policies,
            Set<TermLabel> newLabels, TermLabel label) {
        TermLabelPolicy policy = policies.get(label.name());
        if (policy != null) {
            label = policy.keepLabel(state, services, applicationPosInOccurrence, applicationTerm,
                rule, goal, hint, tacletTerm, newTerm, label);
            if (label != null) {
                newLabels.add(label);
            }
        }
    }

    /**
     * <p>
     * Computes active {@link ChildTermLabelPolicy} instances which have to be executed during the
     * given rule application.
     * </p>
     * <p>
     * This is a helper {@link Map} of
     * {@link #instantiateLabels(TermLabelState, Services, PosInOccurrence, Rule, RuleApp, Goal, Object, Term, Term)}
     * </p>
     *
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional {@link Term} in the taclet which is responsible to instantiate
     *        the new {@link Term} for the new proof node or {@code null} in case of built in rules.
     * @param newTerm the template for the new {@link Term} to create
     * @param ruleSpecificPolicies Rule specific {@link ChildTermLabelPolicy} instances.
     * @param ruleIndependentPolicies All rules {@link ChildTermLabelPolicy} instances.
     * @return The active {@link ChildTermLabelPolicy} which have to be performed.
     */
    protected Map<Name, ChildTermLabelPolicy> computeActiveChildPolicies(TermServices services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm, Term newTerm,
            Map<Name, Map<Name, ChildTermLabelPolicy>> ruleSpecificPolicies,
            Map<Name, ChildTermLabelPolicy> ruleIndependentPolicies) {
        Map<Name, ChildTermLabelPolicy> activeDirectChildPolicies =
            new LinkedHashMap<>();
        if (rule != null) {
            Map<Name, ChildTermLabelPolicy> rulePolicies = ruleSpecificPolicies.get(rule.name());
            if (rulePolicies != null) {
                for (Entry<Name, ChildTermLabelPolicy> entry : rulePolicies.entrySet()) {
                    if (entry.getValue().isRuleApplicationSupported(services,
                        applicationPosInOccurrence, applicationTerm, rule, goal, hint, tacletTerm,
                        newTerm)) {
                        activeDirectChildPolicies.put(entry.getKey(), entry.getValue());
                    }
                }
            }
        }
        if (!ruleIndependentPolicies.isEmpty()) {
            for (Entry<Name, ChildTermLabelPolicy> entry : ruleIndependentPolicies.entrySet()) {
                if (entry.getValue().isRuleApplicationSupported(services,
                    applicationPosInOccurrence, applicationTerm, rule, goal, hint, tacletTerm,
                    newTerm)) {
                    activeDirectChildPolicies.put(entry.getKey(), entry.getValue());
                }
            }
        }
        return activeDirectChildPolicies;
    }

    /**
     * <p>
     * Performs the given direct {@link ChildTermLabelPolicy} instances.
     * </p>
     * <p>
     * This is a helper {@link Map} of
     * {@link #instantiateLabels(TermLabelState, Services, PosInOccurrence, Rule, RuleApp, Goal, Object, Term, Term)}
     * </p>
     *
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional {@link Term} in the taclet which is responsible to instantiate
     *        the new {@link Term} for the new proof node or {@code null} in case of built in rules.
     * @param newTerm the template for the new {@link Term} to create
     * @param policies The {@link ChildTermLabelPolicy} instances to perform.
     * @param newLabels The result {@link Set} with the {@link TermLabel}s of the new {@link Term}.
     */
    protected void performDirectChildPolicies(TermServices services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm, Term newTerm,
            Map<Name, ChildTermLabelPolicy> policies, Set<TermLabel> newLabels) {
        for (Term child : applicationTerm.subs()) {
            for (TermLabel label : child.getLabels()) {
                ChildTermLabelPolicy policy = policies.get(label.name());
                if (policy != null && policy.addLabel(services, applicationPosInOccurrence,
                    applicationTerm, rule, goal, hint, tacletTerm, newTerm, child, label)) {
                    newLabels.add(label);
                }
            }
        }
    }

    /**
     * <p>
     * Performs the given child and grandchild {@link ChildTermLabelPolicy} instances.
     * </p>
     * <p>
     * This is a helper {@link Map} of
     * {@link #instantiateLabels(TermLabelState, Services, PosInOccurrence, Rule, RuleApp, Goal, Object, Term, Term)}
     * </p>
     *
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional {@link Term} in the taclet which is responsible to instantiate
     *        the new {@link Term} for the new proof node or {@code null} in case of built in rules.
     * @param newTerm the template for the new {@link Term} to create
     * @param policies The {@link ChildTermLabelPolicy} instances to perform.
     * @param newLabels The result {@link Set} with the {@link TermLabel}s of the new {@link Term}.
     */
    protected void performChildAndGrandchildPolicies(final TermServices services,
            final PosInOccurrence applicationPosInOccurrence, final Term applicationTerm,
            final Rule rule, final Goal goal, final Object hint, final Term tacletTerm,
            final Term newTerm, final Map<Name, ChildTermLabelPolicy> policies,
            final Set<TermLabel> newLabels) {
        applicationTerm.execPreOrder(new DefaultVisitor() {
            @Override
            public void visit(Term visited) {
                if (visited != applicationTerm) {
                    for (TermLabel label : visited.getLabels()) {
                        ChildTermLabelPolicy policy = policies.get(label.name());
                        if (policy != null && policy.addLabel(services, applicationPosInOccurrence,
                            applicationTerm, rule, goal, hint, tacletTerm, newTerm, visited,
                            label)) {
                            newLabels.add(label);
                        }
                    }
                }
            }
        });
    }

    /**
     * <p>
     * Performs the given child and grandchild {@link TermLabelUpdate} instances.
     * </p>
     * <p>
     * This is a helper {@link Map} of
     * {@link #instantiateLabels(TermLabelState, Services, PosInOccurrence, Rule, RuleApp, Goal, Object, Term, Term)}
     * </p>
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param modalityTerm The optional modality {@link Term}.
     * @param rule The {@link Rule} which is applied.
     * @param ruleApp The {@link RuleApp} which is currently performed.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional {@link Term} in the taclet which is responsible to instantiate
     *        the new {@link Term} for the new proof node or {@code null} in case of built in rules.
     * @param newTerm the template for the new {@link Term} to create
     * @param newLabels The result {@link Set} with the {@link TermLabel}s of the new {@link Term}.
     */
    protected void performUpdater(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Term modalityTerm,
            Rule rule, RuleApp ruleApp, Object hint, Term tacletTerm, Term newTerm,
            ImmutableList<TermLabelUpdate> updater,
            Set<TermLabel> newLabels) {
        for (TermLabelUpdate update : updater) {
            update.updateLabels(state, services, applicationPosInOccurrence, applicationTerm,
                modalityTerm, rule, ruleApp, hint, tacletTerm, newTerm, newLabels);
        }
    }

    /**
     * Refactors all labels on the {@link PosInOccurrence} in the given {@link Term} of a
     * {@link SequentFormula}.
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional taclet {@link Term}.
     * @return The updated application {@link Term}.
     */
    public static Term refactorSequentFormula(TermLabelState state, Services services,
            Term sequentFormula, PosInOccurrence applicationPosInOccurrence, Rule rule, Goal goal,
            Object hint, Term tacletTerm) {
        TermLabelManager manager = getTermLabelManager(services);
        if (manager != null) {
            return manager.refactorSequentFormula(state, services, sequentFormula,
                applicationPosInOccurrence, goal, hint, rule, tacletTerm);
        } else {
            return sequentFormula;
        }
    }

    /**
     * Refactors all labels on the {@link PosInOccurrence} in the given {@link Term} of a
     * {@link SequentFormula}.
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param rule The {@link Rule} which is applied.
     * @param tacletTerm The optional taclet {@link Term}.
     * @return The updated application {@link Term}.
     */
    public Term refactorSequentFormula(TermLabelState state, Services services, Term sequentFormula,
            PosInOccurrence applicationPosInOccurrence, Goal goal, Object hint, Rule rule,
            Term tacletTerm) {
        final PosInTerm pos = applicationPosInOccurrence.posInTerm();
        final Term oldTerm = pos.getSubTerm(sequentFormula);
        // Compute active refactorings
        RefactoringsContainer refactorings = computeRefactorings(state, services,
            applicationPosInOccurrence, oldTerm, rule, goal, hint, tacletTerm);
        // Perform refactoring
        Term newTerm = refactorApplicationTerm(state, services, applicationPosInOccurrence, oldTerm,
            rule, goal, hint, tacletTerm, refactorings, services.getTermFactory());
        if (newTerm != null && !newTerm.equals(oldTerm)) {
            return replaceTerm(state, applicationPosInOccurrence, newTerm,
                services.getTermFactory(),
                refactorings.childAndGrandchildRefactoringsAndParents(), services,
                applicationPosInOccurrence, oldTerm, rule, goal, hint, tacletTerm);
        } else if (!refactorings.childAndGrandchildRefactoringsAndParents().isEmpty()) {
            return replaceTerm(state, applicationPosInOccurrence, oldTerm,
                services.getTermFactory(),
                refactorings.childAndGrandchildRefactoringsAndParents(), services,
                applicationPosInOccurrence, oldTerm, rule, goal, hint, tacletTerm);
        } else {
            return sequentFormula;
        }
    }

    /**
     * <p>
     * Refactors all labels in the complete {@link Sequent}. This is the last step of each rule
     * application.
     * </p>
     * <p>
     * This method delegates the request to the {@link TermLabelManager} of the given
     * {@link Services} if possible. Otherwise no labels are returned.
     * </p>
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional taclet {@link Term}.
     * @return The updated application {@link Term}.
     */
    public static Term refactorTerm(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm) {
        TermLabelManager manager = getTermLabelManager(services);
        if (manager != null) {
            return manager.refactorTerm(state, services, applicationPosInOccurrence,
                applicationTerm, goal, hint, rule, tacletTerm);
        } else {
            return applicationTerm;
        }
    }

    /**
     * Refactors all labels in the given application {@link Term}.
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param rule The {@link Rule} which is applied.
     * @param tacletTerm The optional taclet {@link Term}.
     * @return The updated application {@link Term}.
     */
    public Term refactorTerm(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Goal goal,
            Object hint, Rule rule, Term tacletTerm) {
        // Compute active refactorings
        RefactoringsContainer refactorings = computeRefactorings(state, services,
            applicationPosInOccurrence, applicationTerm, rule, goal, hint, tacletTerm);
        // Refactor application term
        Term newApplicationTerm =
            refactorApplicationTerm(state, services, applicationPosInOccurrence, applicationTerm,
                rule, goal, hint, tacletTerm, refactorings, services.getTermFactory());
        return newApplicationTerm != null ? newApplicationTerm : applicationTerm;
    }

    /**
     * <p>
     * Refactors all labels in the complete {@link Sequent}. This is the last step of each rule
     * application.
     * </p>
     * <p>
     * This method delegates the request to the {@link TermLabelManager} of the given
     * {@link Services} if possible. Otherwise no labels are returned.
     * </p>
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional taclet {@link Term}.
     */
    public static void refactorGoal(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Rule rule, Goal goal, Object hint,
            Term tacletTerm) {
        TermLabelManager manager = getTermLabelManager(services);
        if (manager != null) {
            Term applicationTerm =
                applicationPosInOccurrence != null ? applicationPosInOccurrence.subTerm() : null;
            manager.refactorGoal(state, services, applicationPosInOccurrence, applicationTerm, rule,
                goal, hint, tacletTerm);
        }
    }

    /**
     * <p>
     * Refactors all labels in the complete {@link Sequent}. This is the last step of each rule
     * application.
     * </p>
     * <p>
     * This method delegates the request to the {@link TermLabelManager} of the given
     * {@link Services} if possible. Otherwise no labels are returned.
     * </p>
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional taclet {@link Term}.
     */
    public void refactorGoal(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm) {
        // Compute active refactorings
        RefactoringsContainer refactorings = computeRefactorings(state, services,
            applicationPosInOccurrence, applicationTerm, rule, goal, hint, tacletTerm);
        // Refactor application term
        final TermFactory tf = services.getTermFactory();
        Term newApplicationTerm =
            refactorApplicationTerm(state, services, applicationPosInOccurrence, applicationTerm,
                rule, goal, hint, tacletTerm, refactorings, tf);
        if (newApplicationTerm != null && !newApplicationTerm.equals(applicationTerm)) {
            Term root = replaceTerm(state, applicationPosInOccurrence, newApplicationTerm, tf,
                refactorings.childAndGrandchildRefactoringsAndParents(), services,
                applicationPosInOccurrence, newApplicationTerm, rule, goal, hint, tacletTerm);
            goal.changeFormula(new SequentFormula(root), applicationPosInOccurrence.topLevel());
        } else if (!refactorings.childAndGrandchildRefactoringsAndParents().isEmpty()) {
            Term root = replaceTerm(state, applicationPosInOccurrence, applicationTerm, tf,
                refactorings.childAndGrandchildRefactoringsAndParents(), services,
                applicationPosInOccurrence, newApplicationTerm, rule, goal, hint, tacletTerm);
            goal.changeFormula(new SequentFormula(root), applicationPosInOccurrence.topLevel());
        }
        // Do sequent refactoring if required
        if (!refactorings.sequentRefactorings().isEmpty() && goal != null) {
            Sequent sequent = goal.sequent();
            refactorSemisequent(state, services, applicationPosInOccurrence, applicationTerm, rule,
                goal, hint, tacletTerm, sequent.antecedent(), true,
                refactorings.sequentRefactorings());
            refactorSemisequent(state, services, applicationPosInOccurrence, applicationTerm, rule,
                goal, hint, tacletTerm, sequent.succedent(), false,
                refactorings.sequentRefactorings());
        }
    }

    /**
     * <p>
     * Refactors all labels in the complete {@link Sequent}. This is the last step of each rule
     * application. Only refactorings with scope {@link RefactoringScope#SEQUENT} are performed!
     * </p>
     * <p>
     * This method delegates the request to the {@link TermLabelManager} of the given
     * {@link Services} if possible. Otherwise no labels are returned.
     * </p>
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional taclet {@link Term}.
     */
    public static void refactorSequent(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Rule rule, Goal goal, Object hint,
            Term tacletTerm) {
        TermLabelManager manager = getTermLabelManager(services);
        if (manager != null) {
            Term applicationTerm =
                applicationPosInOccurrence != null ? applicationPosInOccurrence.subTerm() : null;
            manager.refactorSequent(state, services, applicationPosInOccurrence, applicationTerm,
                rule, goal, hint, tacletTerm);
        }
    }

    /**
     * <p>
     * Refactors all labels in the complete {@link Sequent}. This is the last step of each rule
     * application. Only refactorings with scope {@link RefactoringScope#SEQUENT} are performed!
     * </p>
     * <p>
     * This method delegates the request to the {@link TermLabelManager} of the given
     * {@link Services} if possible. Otherwise no labels are returned.
     * </p>
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional taclet {@link Term}.
     */
    public void refactorSequent(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm) {
        // Compute active refactorings
        RefactoringsContainer refactorings = computeRefactorings(state, services,
            applicationPosInOccurrence, applicationTerm, rule, goal, hint, tacletTerm);
        // Do sequent refactoring if required
        if (!refactorings.sequentRefactorings().isEmpty()) {
            Sequent sequent = goal.sequent();
            refactorSemisequent(state, services, applicationPosInOccurrence, applicationTerm, rule,
                goal, hint, tacletTerm, sequent.antecedent(), true,
                refactorings.sequentRefactorings());
            refactorSemisequent(state, services, applicationPosInOccurrence, applicationTerm, rule,
                goal, hint, tacletTerm, sequent.succedent(), false,
                refactorings.sequentRefactorings());
        }
    }

    /**
     * Replaces the {@link Term} at the specified {@link PosInOccurrence}.
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param pio The {@link PosInOccurrence} to replace {@link Term} at.
     * @param newTerm The new {@link Term} to set.
     * @param tf The {@link TermFactory} to use.
     * @param parentRefactorings The {@link RefactoringsContainer} to consider.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional taclet {@link Term}.
     * @return The root of the {@link PosInOccurrence} containing the new {@link Term} at the
     *         specified {@link PosInOccurrence}.
     */
    protected Term replaceTerm(TermLabelState state, PosInOccurrence pio, Term newTerm,
            TermFactory tf, Set<TermLabelRefactoring> parentRefactorings,
            Services services, PosInOccurrence applicationPosInOccurrence, Term applicationTerm,
            Rule rule, Goal goal, Object hint, Term tacletTerm) {
        do {
            if (pio.isTopLevel()) {
                pio = null;
            } else {
                int childIndex = pio.getIndex();
                pio = pio.up();
                Term newChild = newTerm;
                newTerm = pio.subTerm();
                ImmutableArray<TermLabel> newLabels;
                if (!parentRefactorings.isEmpty()) {
                    newLabels = performRefactoring(state, services, applicationPosInOccurrence,
                        applicationTerm, rule, goal, hint, tacletTerm, newTerm, parentRefactorings);
                } else {
                    newLabels = newTerm.getLabels();
                }
                Term[] newSubs = newTerm.subs().toArray(new Term[newTerm.arity()]);
                newSubs[childIndex] = newChild;
                ImmutableArray<Term> newSubsImmutable = new ImmutableArray<>(newSubs);

                if (!newSubsImmutable.equals(newTerm.subs())
                        || !newLabels.equals(newTerm.getLabels())) {
                    newTerm = tf.createTerm(newTerm.op(), newSubsImmutable, newTerm.boundVars(),
                        newLabels);
                }
            }
        } while (pio != null);
        return newTerm;
    }

    /**
     * Computes the rule-independent {@link TermLabelRefactoring} to consider.
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional taclet {@link Term}.
     * @param refactorings The already accumulated refactorings to be expanded with rule specific
     *        refactorings
     */
    private void determineAndCollectRuleSpecificRefactorings(TermLabelState state,
            Services services, PosInOccurrence applicationPosInOccurrence, Term applicationTerm,
            Rule rule, Goal goal, Object hint, Term tacletTerm,
            RefactoringsContainer refactorings) {
        if (rule != null) {
            ImmutableList<TermLabelRefactoring> ruleRefactorings =
                ruleSpecificRefactorings.get(rule.name());
            if (ruleRefactorings != null) {
                for (TermLabelRefactoring refactoring : ruleRefactorings) {
                    RefactoringScope scope = refactoring.defineRefactoringScope(state, services,
                        applicationPosInOccurrence, applicationTerm, rule, goal, hint, tacletTerm);
                    if (RefactoringScope.SEQUENT.equals(scope)) {
                        refactorings.sequentRefactorings.add(refactoring);
                    } else if (RefactoringScope.APPLICATION_BELOW_UPDATES.equals(scope)) {
                        refactorings.belowUpdatesRefactorings.add(refactoring);
                    } else if (RefactoringScope.APPLICATION_CHILDREN_AND_GRANDCHILDREN_SUBTREE
                            .equals(scope)) {
                        refactorings.childAndGrandchildRefactorings.add(refactoring);
                    } else if (RefactoringScope.APPLICATION_DIRECT_CHILDREN.equals(scope)) {
                        refactorings.directChildRefactorings.add(refactoring);
                    } else if (RefactoringScope.APPLICATION_CHILDREN_AND_GRANDCHILDREN_SUBTREE_AND_PARENTS
                            .equals(scope)) {
                        refactorings.childAndGrandchildRefactoringsAndParents.add(refactoring);
                    }
                }
            }
        }
    }

    /**
     * Computes the rule-independent {@link TermLabelRefactoring} to consider.
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional taclet {@link Term}.
     * @param refactorings The already accumulated refactorings to be expanded with rule independent
     *        refactorings
     */
    private void determineAndRuleIndependentRefactorings(TermLabelState state,
            Services services, PosInOccurrence applicationPosInOccurrence,
            Term applicationTerm,
            Rule rule, Goal goal, Object hint, Term tacletTerm,
            RefactoringsContainer refactorings) {
        for (TermLabelRefactoring refactoring : allRulesRefactorings) {
            RefactoringScope scope = refactoring.defineRefactoringScope(state, services,
                applicationPosInOccurrence, applicationTerm, rule, goal, hint, tacletTerm);
            if (RefactoringScope.SEQUENT.equals(scope)) {
                refactorings.sequentRefactorings.add(refactoring);
            } else if (RefactoringScope.APPLICATION_BELOW_UPDATES.equals(scope)) {
                refactorings.belowUpdatesRefactorings.add(refactoring);
            } else if (RefactoringScope.APPLICATION_CHILDREN_AND_GRANDCHILDREN_SUBTREE
                    .equals(scope)) {
                refactorings.childAndGrandchildRefactorings.add(refactoring);
            } else if (RefactoringScope.APPLICATION_DIRECT_CHILDREN.equals(scope)) {
                refactorings.directChildRefactorings.add(refactoring);
            } else if (RefactoringScope.APPLICATION_CHILDREN_AND_GRANDCHILDREN_SUBTREE_AND_PARENTS
                    .equals(scope)) {
                refactorings.childAndGrandchildRefactoringsAndParents.add(refactoring);
            }
        }
    }

    /**
     * Computes the {@link TermLabelRefactoring} to consider.
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional taclet {@link Term}.
     * @return The {@link RefactoringsContainer} with the {@link TermLabelRefactoring}s to consider.
     */
    protected RefactoringsContainer computeRefactorings(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm) {
        final RefactoringsContainer refactorings = new RefactoringsContainer();
        determineAndCollectRuleSpecificRefactorings(state, services, applicationPosInOccurrence,
            applicationTerm, rule, goal, hint, tacletTerm, refactorings);
        determineAndRuleIndependentRefactorings(state, services, applicationPosInOccurrence,
            applicationTerm, rule, goal, hint, tacletTerm, refactorings);
        return refactorings;
    }

    /**
     * Utility class used by
     * {@link TermLabelManager#computeRefactorings(TermLabelState, Services, PosInOccurrence, Term, Rule, Goal, Object, Term)}
     *
     * @param sequentRefactorings                      The {@link TermLabelRefactoring} for {@link RefactoringScope#SEQUENT}.
     * @param belowUpdatesRefactorings                 The {@link TermLabelRefactoring} for {@link RefactoringScope#APPLICATION_BELOW_UPDATES}.
     * @param childAndGrandchildRefactorings           The {@link TermLabelRefactoring} for
     *                                                 {@link RefactoringScope#APPLICATION_CHILDREN_AND_GRANDCHILDREN_SUBTREE}.
     * @param childAndGrandchildRefactoringsAndParents The {@link TermLabelRefactoring} for
     *                                                 {@link RefactoringScope#APPLICATION_CHILDREN_AND_GRANDCHILDREN_SUBTREE_AND_PARENTS}.
     * @param directChildRefactorings                  The {@link TermLabelRefactoring} for
     *                                                 {@link RefactoringScope#APPLICATION_DIRECT_CHILDREN}.
     * @author Martin Hentschel
     */
    protected record RefactoringsContainer(Set<TermLabelRefactoring> sequentRefactorings,
                                           Set<TermLabelRefactoring> belowUpdatesRefactorings,
                                           Set<TermLabelRefactoring> childAndGrandchildRefactorings,
                                           Set<TermLabelRefactoring> childAndGrandchildRefactoringsAndParents,
                                           Set<TermLabelRefactoring> directChildRefactorings) {
        public RefactoringsContainer() {
            this(new LinkedHashSet<>(), new LinkedHashSet<>(), new LinkedHashSet<>(),
                    new LinkedHashSet<>(), new LinkedHashSet<>());
        }

        /**
         * Returns all {@link TermLabelRefactoring}s which operate on application child and grand
         * children, which are {@link #childAndGrandchildRefactorings ()} and
         * {@link #childAndGrandchildRefactoringsAndParents ()}.
         *
         * @return The combined {@link ImmutableList}.
         */
        public Set<TermLabelRefactoring> getAllApplicationChildAndGrandchildRefactorings() {
            final LinkedHashSet<TermLabelRefactoring> result =
                    new LinkedHashSet<>(childAndGrandchildRefactorings);
            result.addAll(childAndGrandchildRefactoringsAndParents);
            return result;
        }
    }

    /**
     * Do direct child refactoring if required.
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional taclet {@link Term}.
     * @param refactorings The {@link RefactoringsContainer} with the {@link TermLabelRefactoring}s
     *        to consider.
     * @param tf The {@link TermFactory} to create the term.
     * @return The new application {@link Term} or {@code null} if no refactoring was performed.
     */
    private Term refactorChildTerms(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm, RefactoringsContainer refactorings, TermFactory tf) {
        Term newApplicationTerm = applicationTerm;
        if (!refactorings.directChildRefactorings().isEmpty()) {
            boolean changed = false;
            Term[] newSubs = new Term[newApplicationTerm.arity()];
            for (int i = 0; i < newSubs.length; i++) {
                final Term sub = newApplicationTerm.sub(i);
                ImmutableArray<TermLabel> newLabels = performRefactoring(state, services,
                    applicationPosInOccurrence, applicationTerm, rule, goal, hint, tacletTerm, sub,
                    refactorings.directChildRefactorings());

                if (newLabels != sub.getLabels()) {
                    newSubs[i] =
                        tf.createTerm(sub.op(), sub.subs(), sub.boundVars(),
                            newLabels);
                    changed = true;
                } else {
                    newSubs[i] = sub;
                }
            }
            newApplicationTerm = changed ? tf.createTerm(newApplicationTerm.op(), newSubs,
                newApplicationTerm.boundVars(),
                newApplicationTerm.getLabels()) : applicationTerm;
        }
        return newApplicationTerm;
    }


    /**
     * Perform below-updates refactoring if required.
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional taclet {@link Term}.
     * @param refactorings The {@link RefactoringsContainer} with the {@link TermLabelRefactoring}s
     *        to consider.
     * @param tf The {@link TermFactory} to create the term.
     * @param newApplicationTerm The refactored application term until now.
     * @return The new application {@link Term} or {@code null} if no refactoring was performed.
     */
    private Term refactorBelowUpdates(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm, RefactoringsContainer refactorings, TermFactory tf,
            Term newApplicationTerm) {
        if (!refactorings.belowUpdatesRefactorings().isEmpty()) {
            Pair<ImmutableList<Term>, Term> pair = TermBuilder.goBelowUpdates2(newApplicationTerm);
            ImmutableArray<TermLabel> newLabels = performRefactoring(state, services,
                applicationPosInOccurrence, applicationTerm, rule, goal, hint, tacletTerm,
                pair.second, refactorings.belowUpdatesRefactorings());
            if (newLabels != pair.second.getLabels()) {
                Term newModality = tf.createTerm(pair.second.op(), pair.second.subs(),
                    pair.second.boundVars(), newLabels);
                newApplicationTerm =
                    services.getTermBuilder().applyParallel(pair.first, newModality,
                        newApplicationTerm.getLabels());
            }
        }
        return newApplicationTerm;
    }

    /**
     * Do child and grandchild refactoring if required.
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional taclet {@link Term}.
     * @param refactorings The {@link RefactoringsContainer} with the {@link TermLabelRefactoring}s
     *        to consider.
     * @param tf The {@link TermFactory} to create the term.
     * @param newApplicationTerm The refactored application term until now.
     * @return The new application {@link Term} or {@code null} if no refactoring was performed.
     */
    private Term refactorChildrenRecursively(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm, RefactoringsContainer refactorings, TermFactory tf,
            Term newApplicationTerm) {
        final Set<TermLabelRefactoring> allChildAndGrandchildRefactorings =
            refactorings.getAllApplicationChildAndGrandchildRefactorings();
        if (!allChildAndGrandchildRefactorings.isEmpty()) {
            boolean changed = false;
            Term[] newSubs = new Term[newApplicationTerm.arity()];
            for (int i = 0; i < newSubs.length; i++) {
                Term sub = newApplicationTerm.sub(i);
                newSubs[i] = refactorLabelsRecursive(state, services, applicationPosInOccurrence,
                    applicationTerm, rule, goal, hint, tacletTerm, sub,
                    allChildAndGrandchildRefactorings);
                if (!newSubs[i].equals(sub)) {
                    changed = true;
                }
            }
            newApplicationTerm = changed ? tf.createTerm(newApplicationTerm.op(), newSubs,
                newApplicationTerm.boundVars(),
                newApplicationTerm.getLabels()) : newApplicationTerm;
        }
        return newApplicationTerm;
    }


    /**
     * Refactors the labels of the application term.
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional taclet {@link Term}.
     * @param refactorings The {@link RefactoringsContainer} with the {@link TermLabelRefactoring}s
     *        to consider.
     * @param tf The {@link TermFactory} to create the term.
     * @return The new application {@link Term} or {@code null} if no refactoring was performed.
     */
    protected Term refactorApplicationTerm(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm, RefactoringsContainer refactorings, TermFactory tf) {
        if (applicationTerm != null && (!refactorings.directChildRefactorings().isEmpty()
                || !refactorings.childAndGrandchildRefactorings().isEmpty()
                || !refactorings.belowUpdatesRefactorings().isEmpty())) {
            Term newApplicationTerm;
            // Do direct child refactoring if required
            newApplicationTerm = refactorChildTerms(state, services, applicationPosInOccurrence,
                applicationTerm, rule, goal, hint, tacletTerm, refactorings, tf);
            // Perform below-updates refactoring
            newApplicationTerm =
                refactorBelowUpdates(state, services, applicationPosInOccurrence, applicationTerm,
                    rule, goal, hint, tacletTerm, refactorings, tf, newApplicationTerm);
            // Do child and grandchild refactoring if required
            newApplicationTerm = refactorChildrenRecursively(state, services,
                applicationPosInOccurrence, applicationTerm, rule, goal, hint, tacletTerm,
                refactorings, tf, newApplicationTerm);
            return newApplicationTerm;
        } else {
            return null;
        }
    }

    /**
     * Performs a {@link TermLabel} refactoring on the given {@link Semisequent}.
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional taclet {@link Term}.
     * @param semisequent The {@link Semisequent} to refactor.
     * @param inAntec {@code true} antecedent, {@code false} succedent.
     * @param activeRefactorings The active {@link TermLabelRefactoring}s to execute.
     */
    protected void refactorSemisequent(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm, Semisequent semisequent, boolean inAntec,
            Set<TermLabelRefactoring> activeRefactorings) {
        if (!activeRefactorings.isEmpty()) {
            for (SequentFormula sfa : semisequent) {
                Term updatedTerm =
                    refactorLabelsRecursive(state, services, applicationPosInOccurrence,
                        applicationTerm, rule, goal, hint, tacletTerm, sfa.formula(),
                        activeRefactorings);
                if (!sfa.formula().equals(updatedTerm)) {
                    goal.changeFormula(new SequentFormula(updatedTerm),
                        new PosInOccurrence(sfa, PosInTerm.getTopLevel(), inAntec));
                }
            }
        }
    }

    /**
     * Performs a {@link TermLabel} refactoring recursively on the given {@link Term}.
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional taclet {@link Term}.
     * @param term The {@link Term} to refactor.
     * @param activeRefactorings The active {@link TermLabelRefactoring}s to execute.
     * @return The refactored {@link Term} in which the {@link TermLabel}s may have changed.
     */
    protected Term refactorLabelsRecursive(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm, Term term,
            Set<TermLabelRefactoring> activeRefactorings) {
        boolean subsChanged = false;
        Term[] newSubs = new Term[term.arity()];
        for (int i = 0; i < newSubs.length; i++) {
            Term oldSub = term.sub(i);
            newSubs[i] = refactorLabelsRecursive(state, services, applicationPosInOccurrence,
                applicationTerm, rule, goal, hint, tacletTerm, oldSub, activeRefactorings);
            if (!newSubs[i].equals(oldSub)) {
                subsChanged = true;
            }
        }
        ImmutableArray<TermLabel> newLabels =
            performRefactoring(state, services, applicationPosInOccurrence, applicationTerm, rule,
                goal, hint, tacletTerm, term, activeRefactorings);
        return subsChanged || newLabels != term.getLabels() ? services.getTermFactory()
                .createTerm(term.op(), newSubs, term.boundVars(), newLabels)
                : term;
    }

    /**
     * Computes the new labels as part of the refactoring for the given {@link Term}.
     *
     * @param state The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is
     *        applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent}
     *        which defines the {@link Term} that is rewritten.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the
     *        previous {@link Sequent}.
     * @param rule The {@link Rule} which is applied.
     * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
     * @param hint An optional hint passed from the active rule to describe the term which should be
     *        created.
     * @param tacletTerm The optional taclet {@link Term}.
     * @param term The {@link Term} to refactor.
     * @param activeRefactorings The active {@link TermLabelRefactoring}s to execute.
     * @return The new {@link TermLabel} which should be used for the given {@link Term}.
     */
    protected ImmutableArray<TermLabel> performRefactoring(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm, Term term,
            Set<TermLabelRefactoring> activeRefactorings) {
        // Create list with all old labels
        LabelCollection newLabels = new LabelCollection(term.getLabels());
        // Give all TermLabelInstantiator instances the chance to remove or to
        // add labels from/to the list
        for (TermLabelRefactoring refactoring : activeRefactorings) {
            refactoring.refactorLabels(state, services, applicationPosInOccurrence, applicationTerm,
                rule, goal, hint, tacletTerm, term, newLabels);
        }
        if (newLabels.isModified()) {
            return new ImmutableArray<>(newLabels.getLabels());
        } else {
            return term.getLabels();
        }
    }

    /**
     * Instances of this class are used to group everything which is required to support one
     * specific {@link TermLabel}.
     *
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
         * The direct {@link ChildTermLabelPolicy} instances to use.
         */
        private final ImmutableList<ChildTermLabelPolicy> directChildTermLabelPolicies;

        /**
         * The child and grandchild {@link ChildTermLabelPolicy} instances to use.
         */
        private final ImmutableList<ChildTermLabelPolicy> childAndGrandchildTermLabelPolicies;

        /**
         * The {@link TermLabelUpdate} instances.
         */
        private final ImmutableList<TermLabelUpdate> termLabelUpdates;

        /**
         * The {@link TermLabelRefactoring} instances.
         */
        private final ImmutableList<TermLabelRefactoring> termLabelRefactorings;

        /**
         * The {@link TermLabelMerger} instance.
         */
        private final TermLabelMerger termLabelMerger;

        /**
         * Constructor.
         *
         * @param termLabelName The {@link Name} of the supported {@link TermLabel}.
         * @param factory The {@link TermLabelFactory} to use.
         */
        public TermLabelConfiguration(Name termLabelName, TermLabelFactory<?> factory) {
            this(termLabelName, factory, null, null, null, null, null, null, null);
        }

        /**
         * Constructor.
         *
         * @param termLabelName The {@link Name} of the supported {@link TermLabel}.
         * @param factory The {@link TermLabelFactory} to use.
         * @param applicationTermPolicies The {@link TermLabelPolicy} instances applied on the
         *        application term.
         * @param modalityTermPolicies The {@link TermLabelPolicy} instances applied on the modality
         *        term.
         * @param directChildTermLabelPolicies The direct {@link ChildTermLabelPolicy} instances to
         *        use.
         * @param childAndGrandchildTermLabelPolicies The child and grandchild
         *        {@link ChildTermLabelPolicy} instances to use.
         * @param termLabelUpdates The {@link TermLabelUpdate} instances.
         * @param termLabelRefactorings The {@link TermLabelRefactoring} instances.
         * @param termLabelMerger The {@link TermLabelMerger} instance.
         */
        public TermLabelConfiguration(Name termLabelName, TermLabelFactory<?> factory,
                ImmutableList<TermLabelPolicy> applicationTermPolicies,
                ImmutableList<TermLabelPolicy> modalityTermPolicies,
                ImmutableList<ChildTermLabelPolicy> directChildTermLabelPolicies,
                ImmutableList<ChildTermLabelPolicy> childAndGrandchildTermLabelPolicies,
                ImmutableList<TermLabelUpdate> termLabelUpdates,
                ImmutableList<TermLabelRefactoring> termLabelRefactorings,
                TermLabelMerger termLabelMerger) {
            assert termLabelName != null;
            assert factory != null;
            this.termLabelName = termLabelName;
            this.factory = factory;
            this.applicationTermPolicies = applicationTermPolicies;
            this.modalityTermPolicies = modalityTermPolicies;
            this.directChildTermLabelPolicies = directChildTermLabelPolicies;
            this.childAndGrandchildTermLabelPolicies = childAndGrandchildTermLabelPolicies;
            this.termLabelUpdates = termLabelUpdates;
            this.termLabelRefactorings = termLabelRefactorings;
            this.termLabelMerger = termLabelMerger;
        }

        /**
         * Returns the {@link Name} of the supported {@link TermLabel}.
         *
         * @return The {@link Name} of the supported {@link TermLabel}.
         */
        public Name getTermLabelName() {
            return termLabelName;
        }

        /**
         * Returns the {@link TermLabelFactory} to use.
         *
         * @return The {@link TermLabelFactory} to use.
         */
        public TermLabelFactory<?> getFactory() {
            return factory;
        }

        /**
         * Returns the {@link TermLabelPolicy} instances applied on the application term.
         *
         * @return The {@link TermLabelPolicy} instances applied on the application term.
         */
        public ImmutableList<TermLabelPolicy> getApplicationTermPolicies() {
            return applicationTermPolicies;
        }

        /**
         * Returns the {@link TermLabelPolicy} instances applied on the modality term.
         *
         * @return The {@link TermLabelPolicy} instances applied on the modality term.
         */
        public ImmutableList<TermLabelPolicy> getModalityTermPolicies() {
            return modalityTermPolicies;
        }

        /**
         * Returns the direct {@link ChildTermLabelPolicy} instances to use.
         *
         * @return The direct {@link ChildTermLabelPolicy} instances to use.
         */
        public ImmutableList<ChildTermLabelPolicy> getDirectChildTermLabelPolicies() {
            return directChildTermLabelPolicies;
        }

        /**
         * Returns the child and grandchild {@link ChildTermLabelPolicy} instances to use.
         *
         * @return The child and grandchild {@link ChildTermLabelPolicy} instances to use.
         */
        public ImmutableList<ChildTermLabelPolicy> getChildAndGrandchildTermLabelPolicies() {
            return childAndGrandchildTermLabelPolicies;
        }

        /**
         * Returns the {@link TermLabelUpdate} instances.
         *
         * @return The {@link TermLabelUpdate} instances.
         */
        public ImmutableList<TermLabelUpdate> getTermLabelUpdates() {
            return termLabelUpdates;
        }

        /**
         * Returns the {@link TermLabelRefactoring} instances.
         *
         * @return The {@link TermLabelRefactoring} instances.
         */
        public ImmutableList<TermLabelRefactoring> getTermLabelRefactorings() {
            return termLabelRefactorings;
        }

        /**
         * Returns the {@link TermLabelMerger} instance.
         *
         * @return The {@link TermLabelMerger} instance.
         */
        public TermLabelMerger getTermLabelMerger() {
            return termLabelMerger;
        }
    }

    /**
     * Searches the innermost {@link TermLabel} wit the given {@link Name} in the parent hierarchy
     * of the {@link PosInOccurrence}.
     *
     * @param pio The {@link PosInOccurrence} to search in.
     * @param termLabelName The {@link Name} of the {@link TermLabel} to search.
     * @return The found {@link TermLabel} or {@code null} if not available.
     */
    public static TermLabel findInnerMostParentLabel(PosInOccurrence pio, Name termLabelName) {
        TermLabel label = null;
        while (label == null && pio != null) {
            Term subTerm = pio.subTerm();
            label = subTerm.getLabel(termLabelName);
            pio = pio.isTopLevel() ? null : pio.up();
        }
        return label;
    }

    /**
     * Merges the {@link TermLabel}s of the rejected {@link SequentFormula}s into the resulting
     * {@link Sequent}.
     *
     * @param currentSequent The {@link SequentChangeInfo} which lists the rejected
     *        {@link SequentFormula}s.
     * @param services The {@link Services} to use.
     */
    public static void mergeLabels(SequentChangeInfo currentSequent, Services services) {
        TermLabelManager manager = getTermLabelManager(services);
        if (manager != null) {
            manager.mergeLabels(services, currentSequent);
        }
    }

    /**
     * Merges the {@link TermLabel}s of the rejected {@link SequentFormula}s into the resulting
     * {@link Sequent}.
     *
     * @param services The {@link Services} to use.
     * @param currentSequent The {@link SequentChangeInfo} which lists the rejected
     *        {@link SequentFormula}s.
     */
    public void mergeLabels(Services services, SequentChangeInfo currentSequent) {
        for (SequentFormula rejectedSF : currentSequent.getSemisequentChangeInfo(true)
                .rejectedFormulas()) {
            mergeLabels(currentSequent, services, rejectedSF, true);
        }
        for (final SequentFormula rejectedSF : currentSequent.getSemisequentChangeInfo(false)
                .rejectedFormulas()) {
            mergeLabels(currentSequent, services, rejectedSF, false);
        }
    }

    /**
     * Merges the {@link TermLabel}s of the given {@link SequentFormula} into the resulting
     * {@link Sequent}.
     *
     * @param currentSequent The {@link SequentChangeInfo} which lists the rejected
     *        {@link SequentFormula}s.
     * @param services The {@link Services} to use.
     * @param rejectedSF The rejected {@link SequentFormula} to work with.
     * @param inAntecedent {@code true} rejected {@link SequentFormula} is in antecedent,
     *        {@code false} it is in succedent.
     */
    protected void mergeLabels(SequentChangeInfo currentSequent, Services services,
            SequentFormula rejectedSF, boolean inAntecedent) {
        final Term rejectedTerm = rejectedSF.formula();
        if (rejectedTerm.hasLabels()) {
            // Search existing SequentFormula
            Semisequent s = currentSequent.getSemisequentChangeInfo(inAntecedent).semisequent();
            SequentFormula existingSF = CollectionUtil.search(s,
                element -> element.formula().equalsModProperty(rejectedTerm,
                    RENAMING_TERM_PROPERTY));
            if (existingSF != null) {
                // Create list of new labels
                Term existingTerm = existingSF.formula();
                List<TermLabel> mergedLabels = new LinkedList<>();
                CollectionUtil.addAll(mergedLabels, existingTerm.getLabels());
                boolean labelsChanged = false;
                // Merge all labels of the rejected term with those of the existing one
                for (TermLabel rejectedLabel : rejectedTerm.getLabels()) {
                    TermLabel existingLabel = existingTerm.getLabel(rejectedLabel.name());
                    // Label is present, solve conflict with help of the TermLabelMerger.
                    TermLabelMerger merger = mergerMap.get(rejectedLabel.name());
                    if (merger != null) {
                        if (merger.mergeLabels(existingSF, existingTerm, existingLabel, rejectedSF,
                            rejectedTerm, rejectedLabel, mergedLabels)) {
                            labelsChanged = true;
                        }
                    }
                }
                // Replace sequent formula
                if (labelsChanged) {
                    Term newTerm = services.getTermFactory().createTerm(existingTerm.op(),
                        existingTerm.subs(), existingTerm.boundVars(),
                        new ImmutableArray<>(mergedLabels));
                    SequentChangeInfo sci =
                        currentSequent.sequent().changeFormula(new SequentFormula(newTerm),
                            new PosInOccurrence(existingSF, PosInTerm.getTopLevel(), inAntecedent));
                    currentSequent.combine(sci);
                }
            }
        }
    }

    /**
     * Remove all irrelevant labels from a term.
     *
     * @param term the term to transform.
     * @param services services.
     * @return the transformed term.
     * @see TermLabel#isProofRelevant()
     */
    public static Term removeIrrelevantLabels(Term term, Services services) {
        if (services.getTermBuilder().getOriginFactory() == null) {
            return term;
        } else {
            return removeIrrelevantLabels(term, services.getTermFactory());
        }
    }

    /**
     * Remove all irrelevant labels from a term.
     *
     * @param term the term to transform.
     * @param tf a term factory.
     * @return the transformed term.
     * @see TermLabel#isProofRelevant()
     */
    public static Term removeIrrelevantLabels(Term term, TermFactory tf) {
        return tf.createTerm(term.op(),
            new ImmutableArray<>(term.subs().stream().map(t -> removeIrrelevantLabels(t, tf))
                    .collect(Collectors.toList())),
            term.boundVars(), new ImmutableArray<>(term.getLabels().stream()
                    .filter(TermLabel::isProofRelevant).collect(Collectors.toList())));
    }
}
