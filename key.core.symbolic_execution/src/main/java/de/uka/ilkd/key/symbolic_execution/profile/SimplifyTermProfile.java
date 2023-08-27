/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.profile;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.SingletonLabelFactory;
import de.uka.ilkd.key.logic.label.TermLabelManager.TermLabelConfiguration;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.label.TermLabelPolicy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.symbolic_execution.strategy.SimplifyTermStrategy;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionStrategy;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

/**
 * An extended {@link JavaProfile} used in side proofs to simplify a {@link Term}.
 *
 * @author Martin Hentschel
 */
public class SimplifyTermProfile extends JavaProfile {
    /**
     * The {@link Name} of this {@link Profile}.
     */
    public static final String NAME = "Java Profile for Term Simplification";

    /**
     * The used {@link StrategyFactory} of the {@link SymbolicExecutionStrategy}.
     */
    private final static StrategyFactory SIDE_PROOF_FACTORY = new SimplifyTermStrategy.Factory();

    /**
     * <p>
     * The default instance of this class.
     * </p>
     * <p>
     * It is typically used in the {@link Thread} of the user interface. Other instances of this
     * class are typically only required to use them in different {@link Thread}s (not the UI
     * {@link Thread}).
     * </p>
     */
    public static SimplifyTermProfile defaultInstance;

    /**
     * Constructor.
     */
    public SimplifyTermProfile() {
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected ImmutableList<TermLabelConfiguration> computeTermLabelConfiguration() {
        ImmutableList<TermLabelConfiguration> result = super.computeTermLabelConfiguration();
        ImmutableList<TermLabelPolicy> symExcPolicies =
            ImmutableSLList.<TermLabelPolicy>nil()
                    .prepend((state, services, applicationPosInOccurrence, applicationTerm, rule,
                            goal, hint, tacletTerm, newTermOp, newTermSubs, newTermBoundVars,
                            newTermJavaBlock, newTermOriginalLabels, label) -> label);
        result = result.prepend(new TermLabelConfiguration(SymbolicExecutionUtil.RESULT_LABEL_NAME,
            new SingletonLabelFactory<>(SymbolicExecutionUtil.RESULT_LABEL), null,
            symExcPolicies, null, null, null, null, null));
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected ImmutableSet<StrategyFactory> getStrategyFactories() {
        return DefaultImmutableSet.<StrategyFactory>nil().add(SIDE_PROOF_FACTORY);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public StrategyFactory getDefaultStrategyFactory() {
        return SIDE_PROOF_FACTORY;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String name() {
        return NAME;
    }

    /**
     * <p>
     * Returns the default instance of this class.
     * </p>
     * <p>
     * It is typically used in the {@link Thread} of the user interface. Other instances of this
     * class are typically only required to use them in different {@link Thread}s (not the UI
     * {@link Thread}).
     * </p>
     *
     * @return The default instance for usage in the {@link Thread} of the user interface.
     */
    public static synchronized SimplifyTermProfile getDefaultInstance() {
        if (defaultInstance == null) {
            defaultInstance = new SimplifyTermProfile();
        }
        return defaultInstance;
    }
}
