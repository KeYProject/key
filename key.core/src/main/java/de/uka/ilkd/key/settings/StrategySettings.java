/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import java.util.Objects;
import java.util.Properties;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.strategy.JavaCardDLStrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;

import org.key_project.logic.Name;
import org.key_project.prover.engine.GoalChooser;
import org.key_project.prover.engine.StopCondition;
import org.key_project.prover.engine.impl.AppliedRuleStopCondition;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


public class StrategySettings extends AbstractSettings {
    public static final Logger LOGGER = LoggerFactory.getLogger(StrategySettings.class);

    public static final String CATEGORY = "Strategy";

    public static final String STRATEGY_KEY = "ActiveStrategy";
    public static final String STEPS_KEY = "MaximumNumberOfAutomaticApplications";
    public static final String TIMEOUT_KEY = "Timeout";
    private static final String PROP_STRATEGY_PROPERTIES = "strategyProperties";


    private Name activeStrategy;

    /**
     * maximal number of automatic rule applications before an interaction is required
     */
    private int maxSteps = 10000;

    /**
     * maximal time in ms after which automatic rule application is aborted
     */
    private long timeout = -1;

    private StrategyProperties strategyProperties = new StrategyProperties();

    /**
     * An optional customized {@link StopCondition} which is used in an {@link ApplyStrategy}
     * instance to determine after each applied rule if more rules should be applied or not.
     */
    private StopCondition<Goal> customApplyStrategyStopCondition;

    /**
     * An optional customized {@link GoalChooser} which is used in an {@link ApplyStrategy} instance
     * to select the next {@link Goal} to apply a rule on. If no one is defined the default one of
     * the {@link ApplyStrategy}, which is defined by the user interface, is used.
     */
    private GoalChooser<Proof, Goal> customApplyStrategyGoalChooser;

    /**
     * returns the maximal amount of heuristics steps before a user interaction is required
     *
     * @return the maximal amount of heuristics steps before a user interaction is required
     */
    public int getMaxSteps() {
        return maxSteps;
    }

    /**
     * sets the maximal amount of heuristic steps before a user interaction is required
     *
     * @param mSteps maximal amount of heuristic steps
     */
    public void setMaxSteps(int mSteps) {
        var old = maxSteps;
        maxSteps = mSteps;
        firePropertyChange(STEPS_KEY, old, maxSteps);
    }

    /**
     * Get the name of the active strategy
     *
     * @return the name of the active strategy
     */
    public Name getStrategy() {
        return activeStrategy;
    }

    /**
     * Set the name of the active strategy
     *
     * @param name the name of teh strategy
     */
    public void setStrategy(Name name) {
        var old = this.activeStrategy;
        activeStrategy = name;
        firePropertyChange(STRATEGY_KEY, old, activeStrategy);
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.gui.Settings#readSettings(java.util.Properties)
     */
    public void readSettings(Properties props) {
        String numString = props.getProperty("[" + CATEGORY + "]" + STEPS_KEY);
        String strategyString = props.getProperty("[" + CATEGORY + "]" + STRATEGY_KEY);
        String timeoutString = props.getProperty("[" + CATEGORY + "]" + TIMEOUT_KEY);

        long localTimeout = -1;
        int numSteps = 10000;

        if (numString != null) {
            try {
                numSteps = Integer.parseInt(numString);
            } catch (NumberFormatException e) {
                LOGGER.debug("StrategySettings: failure while converting the string "
                    + "with the allowed steps of heuristics applications to int."
                    + "Use default value 1000 instead."
                    + "\nThe String that has been tried to convert was {}", numString);
            }
        }

        if (timeoutString != null) {
            try {
                localTimeout = Long.parseLong(timeoutString);
            } catch (NumberFormatException e) {
                LOGGER.debug("StrategySettings: failure while converting the string "
                    + "with rule application timeout. "
                    + "\nThe String that has been tried to convert was {}", timeoutString);
            }
        }

        // set active strategy
        if (strategyString != null) {
            activeStrategy = new Name(strategyString);
        }

        // set strategy options
        setStrategyProperties(StrategyProperties.read(props));

        // set max steps
        setMaxSteps(numSteps);

        // set time out
        setTimeout(localTimeout);
    }

    private void setStrategyProperties(StrategyProperties props) {
        var old = strategyProperties;
        strategyProperties = props;
        firePropertyChange(PROP_STRATEGY_PROPERTIES, old, strategyProperties);
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.gui.Settings#writeSettings(java.util.Properties)
     */
    public void writeSettings(Properties props) {
        if (getStrategy() == null) {
            // It would be better to return the name of the default factory defined by the profile
            // used by the proof
            // in which this strategy settings is used or just not to save the strategy because it
            // is
            // not defined.
            setStrategy(JavaCardDLStrategyFactory.NAME);
        }
        if (maxSteps < 0) {
            setMaxSteps(10000);
        }
        props.setProperty("[" + CATEGORY + "]" + STRATEGY_KEY, getStrategy().toString());
        props.setProperty("[" + CATEGORY + "]" + STEPS_KEY, String.valueOf(getMaxSteps()));
        props.setProperty("[" + CATEGORY + "]" + TIMEOUT_KEY, String.valueOf(getTimeout()));
        strategyProperties.write(props);
    }

    @Override
    public void readSettings(Configuration props) {
        props = props.getSection(CATEGORY);
        if (props == null) {
            return;
        }

        try {
            setMaxSteps(props.getInt(STEPS_KEY));
        } catch (NumberFormatException | NullPointerException e) {
            LOGGER.debug("StrategySettings: failure while converting the string "
                + "with the allowed steps of heuristics applications to int."
                + "Use default value 1000 instead."
                + "\nThe String that has been tried to convert was {}", props.get(STEPS_KEY));
        }

        try {
            setTimeout(props.getInt(TIMEOUT_KEY));
        } catch (NumberFormatException | NullPointerException e) {
            LOGGER.debug("StrategySettings: failure while converting the string "
                + "with rule application timeout. "
                + "\nThe String that has been tried to convert was {}", props.get(TIMEOUT_KEY));
        }

        // set active strategy
        var strategy = props.getString(STRATEGY_KEY);
        if (strategy != null) {
            activeStrategy = new Name(strategy);
        }

        setStrategyProperties(StrategyProperties.read(props));
    }

    @Override
    public void writeSettings(Configuration props) {
        props = props.getOrCreateSection(CATEGORY);
        if (getStrategy() == null) {
            setStrategy(JavaCardDLStrategyFactory.NAME);
        }
        if (maxSteps < 0) {
            setMaxSteps(10000);
        }

        props.set(STRATEGY_KEY, getStrategy().toString());
        props.set(STEPS_KEY, getMaxSteps());
        props.set(TIMEOUT_KEY, getTimeout());

        strategyProperties.write(props);
    }

    /**
     * returns a shallow copy of the strategy properties
     */
    public StrategyProperties getActiveStrategyProperties() {
        return (StrategyProperties) strategyProperties.clone();
    }

    /**
     * sets the strategy properties if different from current ones
     */
    public void setActiveStrategyProperties(StrategyProperties p) {
        var old = this.strategyProperties;
        this.strategyProperties = (StrategyProperties) p.clone();
        firePropertyChange(PROP_STRATEGY_PROPERTIES, old, this.strategyProperties);
    }

    /**
     * retrieves the time in ms after which automatic rule application shall be aborted (-1 disables
     * timeout)
     *
     * @return time in ms after which automatic rule application shall be aborted
     */
    public long getTimeout() {
        return timeout;
    }

    /**
     * sets the time after which automatic rule application shall be aborted (-1 disables timeout)
     *
     * @param timeout a long specifying the timeout in ms
     */
    public void setTimeout(long timeout) {
        var old = this.timeout;
        this.timeout = timeout;
        firePropertyChange(TIMEOUT_KEY, old, timeout);
    }

    /**
     * <p>
     * Returns the {@link StopCondition} to use in an {@link ApplyStrategy} instance to determine
     * after each applied rule if more rules should be applied or not.
     * </p>
     * <p>
     * By default is an {@link AppliedRuleStopCondition} used which stops the auto mode if the given
     * maximal number of rule applications or a defined timeout is reached. If a customized
     * implementation is defined for the current proof via
     * {@link #setCustomApplyStrategyStopCondition(StopCondition)} this instance is returned
     * instead.
     * </p>
     *
     * @return The {@link StopCondition} to use in an {@link ApplyStrategy} instance.
     */
    public StopCondition<Goal> getApplyStrategyStopCondition() {
        return Objects.requireNonNullElseGet(customApplyStrategyStopCondition,
            AppliedRuleStopCondition::new);
    }

    /**
     * Returns a customized {@link StopCondition} which is used in an {@link ApplyStrategy} to
     * determine after each applied rule if more rules should be applied or not.
     *
     * @return The customized {@link StopCondition} or {@code null} if the default one should be
     *         used.
     */
    public StopCondition<Goal> getCustomApplyStrategyStopCondition() {
        return customApplyStrategyStopCondition;
    }

    /**
     * Defines the {@link StopCondition} which is used in an {@link ApplyStrategy} to determine
     * after each applied rule if more rules should be applied or not.
     *
     * @param customApplyStrategyStopCondition The customized {@link StopCondition} to use or
     *        {@code null} to use the default one.
     */
    public void setCustomApplyStrategyStopCondition(
            StopCondition<Goal> customApplyStrategyStopCondition) {
        this.customApplyStrategyStopCondition = customApplyStrategyStopCondition;
    }

    /**
     * Returns the customized {@link GoalChooser} which is used in an {@link ApplyStrategy} instance
     * to select the next {@link Goal} to apply a rule on. If no one is defined the default one of
     * the {@link ApplyStrategy}, which is defined by the user interface, is used.
     *
     * @return The customized {@link GoalChooser} to use or {@code null} to use the default one of
     *         the {@link ApplyStrategy}.
     */
    public GoalChooser<Proof, Goal> getCustomApplyStrategyGoalChooser() {
        return customApplyStrategyGoalChooser;
    }

    /**
     * Sets the customized {@link GoalChooser} which is used in an {@link ApplyStrategy} instance to
     * select the next {@link Goal} to apply a rule on. If no one is defined the default one of the
     * {@link ApplyStrategy}, which is defined by the user interface, is used.
     *
     * @param customGoalChooser The customized {@link GoalChooser} to use or {@code null} to use the
     *        default one of the {@link ApplyStrategy}.
     */
    public void setCustomApplyStrategyGoalChooser(GoalChooser<Proof, Goal> customGoalChooser) {
        this.customApplyStrategyGoalChooser = customGoalChooser;
    }
}
