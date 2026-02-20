/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.UseDependencyContractRule;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.strategy.StrategyFactory;

import org.key_project.logic.Name;
import org.key_project.prover.engine.GoalChooserFactory;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.proof.ProofObject;
import org.key_project.prover.rules.RuleApp;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;

/**
 * <p>
 * This interface provides methods that allow to customize KeY for certain applications. It supports
 * to customize
 * <ul>
 * <li>the rule base to be used</li>
 * <li>the available strategies</li>
 * <li>the goal selection strategy</li>
 * <li>the way how term labels are maintained</li>
 * </ul>
 * <p>
 * Currently this is only rudimentary: possible extensions are
 * <ul>
 * <li>program model to use (java, misrac, csharp)</li>
 * <li>integrate in plug-in framework allow addition of menu entries toolbar buttons etc.</li>
 * </ul>
 * etc.
 * </p>
 * <p>
 * Each {@link Profile} has a unique name {@link #ident()}.
 * </p>
 * <p>
 * It is recommended to have only one instance of each {@link Profile}. The default instances for
 * usage in the {@link Thread} of the user interface are available via
 * {@link JavaProfile#getDefaultInstance()} and
 * {@code SymbolicExecutionJavaProfile#getDefaultInstance()}. Multiple
 * instances are only required if {@link Proof}s are done in parallel (in different
 * {@link Thread}s), because some rules might have a state (at the moment this is only the
 * {@link OneStepSimplifier}).
 * </p>
 * <p>
 * The default {@link Profile} which is used if no profile is programatically (or via a custom
 * problem file) defined is {@link AbstractProfile#getDefaultProfile()}. It can be changed via
 * {@link AbstractProfile#setDefaultProfile(Profile)}.
 * </p>
 */
public interface Profile {

    /**
     * returns the rule source containg all taclets for this profile
     */
    RuleCollection getStandardRules();

    /**
     * the name of this profile used to for storing into key files, and for loading
     */
    String ident();

    /**
     * the name of this profile presentable for humans
     */
    default String displayName() {
        return ident();
    }

    /// A description of this profile for the user
    default String description() {
        return "";
    }

    /**
     * returns the strategy factories for the supported strategies
     */
    ImmutableSet<StrategyFactory> supportedStrategies();

    /**
     * returns the strategy factory for the default strategy of this profile
     */
    StrategyFactory getDefaultStrategyFactory();

    /**
     * returns true if strategy <code>strategyName</code> may be used with this profile.
     *
     * @return supportedStrategies()->exists(s | s.name.equals(strategyName))
     */
    boolean supportsStrategyFactory(Name strategyName);

    /**
     * returns the StrategyFactory for strategy <code>strategyName</code>
     *
     * @param strategyName
     *        the Name of the strategy
     * @return the StrategyFactory to build the demanded strategy
     */
    StrategyFactory getStrategyFactory(Name strategyName);

    /**
     * returns the names of possible goalchoosers to be used by the automatic prover environment
     */
    ImmutableSet<String> supportedGoalChoosers();

    /**
     * returns the default builder for a goal chooser
     */
    <P extends ProofObject<G>, G extends ProofGoal<@NonNull G>> GoalChooserFactory<P, G> getDefaultGoalChooserBuilder();

    /**
     * sets the user selected goal chooser builder to be used as prototype
     *
     * @param name
     *        the String with the name of the goal chooser to be used
     * @throws IllegalArgumentException
     *         if a goal chooser of the given name is not supported
     */
    void setSelectedGoalChooserBuilder(String name);

    /**
     * returns a new builder instance for the selected goal choooser
     */
    <P extends ProofObject<G>, G extends ProofGoal<@NonNull G>> GoalChooserFactory<P, G> getSelectedGoalChooserBuilder();

    /**
     * returns the (default) justification for the given rule
     */
    RuleJustification getJustification(Rule r);


    /**
     * returns the file name of the internal class directory relative to JavaRedux
     *
     * @return the file name of the internal class directory relative to JavaRedux
     */
    String getInternalClassDirectory();

    /**
     * returns the file name of the internal class list
     *
     * @return the file name of the internal class list
     */
    String getInternalClasslistFilename();

    TermLabelManager getTermLabelManager();

    boolean isSpecificationInvolvedInRuleApp(RuleApp app);

    /// Create an instance of a specification repository suitable for the given profile.
    /// For example WD requires a special instance.
    default SpecificationRepository createSpecificationRepository(Services services) {
        return new SpecificationRepository(services);
    }

    /// Returns the implementation of a [UseDependencyContractRule] for this profile.
    ///
    /// @see de.uka.ilkd.key.proof.io.IntermediateProofReplayer
    default UseDependencyContractRule getUseDependencyContractRule() {
        return UseDependencyContractRule.INSTANCE;
    }

    /// Returns the implementation of a [UseOperationContractRule] for this profile
    ///
    /// @see de.uka.ilkd.key.proof.io.IntermediateProofReplayer
    default UseOperationContractRule getUseOperationContractRule() {
        return UseOperationContractRule.INSTANCE;
    }

    /// Let a profile visit a freshly created init profile. Allows the setting of properties after
    /// the
    /// Taclet base has been loaded, but before Java sources are loaded or the environment is
    /// established.
    ///
    /// @see ProblemInitializer
    default void prepareInitConfig(InitConfig baseConfig) {

    }
}
