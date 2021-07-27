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

package de.uka.ilkd.key.settings;

import java.util.EventObject;
import java.util.LinkedList;
import java.util.Properties;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.prover.GoalChooser;
import de.uka.ilkd.key.prover.StopCondition;
import de.uka.ilkd.key.prover.impl.AppliedRuleStopCondition;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.strategy.JavaCardDLStrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.Debug;



public class StrategySettings implements Settings, Cloneable {

    private static final String STRATEGY_KEY = "[Strategy]ActiveStrategy";
    private static final String STEPS_KEY = "[Strategy]MaximumNumberOfAutomaticApplications";
    private static final String TIMEOUT_KEY = "[Strategy]Timeout";
    
    private final LinkedList<SettingsListener> listenerList = 
        new LinkedList<SettingsListener>();
    
    private Name activeStrategy;

    /** maximal number of automatic rule applications before an interaction is required */ 
    private int maxSteps = -1;
    
    /** maximal time in ms after which automatic rule application is aborted */
    private long timeout = -1;
    
    private StrategyProperties strategyProperties = new StrategyProperties();
    
    /**
     * An optional customized {@link StopCondition} which is used in an
     * {@link ApplyStrategy} instance to determine after each applied rule
     * if more rules should be applied or not.
     */
    private StopCondition customApplyStrategyStopCondition;
    
    /**
     * An optional customized {@link GoalChooser} which is used in an
     * {@link ApplyStrategy} instance to select the next {@link Goal} to
     * apply a rule on. If no one is defined the default one of the
     * {@link ApplyStrategy}, which is defined by the user interface, is used.
     */
    private GoalChooser customApplyStrategyGoalChooser;
    
    /** returns the maximal amount of heuristics steps before a user
     * interaction is required 
     * @return the maximal amount of heuristics steps before a user
     * interaction is required
     */
    public int getMaxSteps(){
        return maxSteps;
    }

    /** sets the maximal amount of heuristic steps before a user
     * interaction is required
     * @param mSteps maximal amount of heuristic steps
     */
     public void setMaxSteps(int mSteps) {
         if(maxSteps != mSteps) {
           maxSteps = mSteps;
           fireSettingsChanged();
	 }
     }
     
     /**
      * Get the name of the active strategy
      * @return the name of the active strategy
      */
     public Name getStrategy () {
         return activeStrategy;
     }
     
     /**
      * Set the name of the active strategy
      * @param name
      */
     public void setStrategy ( Name name ) {
         if(!name.equals(activeStrategy)) {
           activeStrategy = name;
           fireSettingsChanged();
	 }
     }
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.gui.Settings#readSettings(java.util.Properties)
     */
    public void readSettings(Properties props) {
        String numString = props.getProperty(STEPS_KEY);
        String strategyString = props.getProperty(STRATEGY_KEY);
        String timeoutString = props.getProperty(TIMEOUT_KEY);
    
        long localTimeout = -1;
        int numSteps = 10000;
    
        if (numString != null){
            try {
                numSteps = Integer.parseInt(numString);
            } catch(NumberFormatException e) { 
                Debug.out("StrategySettings: failure while converting the string "+
                          "with the allowed steps of heuristics applications to int."+
                          "Use default value 1000 instead."+
                          "\nThe String that has been tried to convert was", numString);
            }
        }
        
        if (timeoutString != null) {
            try {
                localTimeout = Long.parseLong(timeoutString);
            } catch(NumberFormatException e) { 
                Debug.out("StrategySettings: failure while converting the string "+
                          "with rule application timeout. "+                        
                          "\nThe String that has been tried to convert was", timeoutString);
            }
        }
        
        // set active strategy
        if (strategyString != null) {
            activeStrategy = new Name (strategyString);
        } 

        // set strategy options
        strategyProperties = StrategyProperties.read(props);
                
        // set max steps
        maxSteps = numSteps;        
        
        // set time out
        this.timeout = localTimeout;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.gui.Settings#writeSettings(java.util.Properties)
     */
    public void writeSettings(Properties props) {
	if (getStrategy()==null) {
	    setStrategy(JavaCardDLStrategyFactory.NAME); // It would be bedder to return the name of the default factory defined by the profile used by the proof in which this strategysettings is used or just not to save the strategy because it is not defined.
	}
	if (maxSteps<0) {
	    setMaxSteps(10000);
	}
        props.setProperty(STRATEGY_KEY, getStrategy().toString());
        props.setProperty(STEPS_KEY,  String.valueOf(getMaxSteps()));
       
        props.setProperty(TIMEOUT_KEY,  String.valueOf(getTimeout()));
        strategyProperties.write(props);              
    }

    /** sends the message that the state of this setting has been
     * changed to its registered listeners (not thread-safe)
     */
    protected void fireSettingsChanged() {
        for (SettingsListener aListenerList : listenerList) {
            aListenerList.settingsChanged(new EventObject(this));
        }
    }

    /** adds a listener to the settings object 
     * @param l the listener
     */
    public void addSettingsListener(SettingsListener l) {
        listenerList.add(l);
    }
    
    public void removeSettingsListener(SettingsListener l) {
        listenerList.remove(l);
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
        if (!p.equals(strategyProperties)) {
            this.strategyProperties = (StrategyProperties) p.clone();  
            fireSettingsChanged();
        }
    }

    /**
     * retrieves the time in ms after which automatic rule application shall be aborted
     * (-1 disables timeout)
     * @return time in ms after which automatic rule application shall be aborted
     */
    public long getTimeout() {
        return timeout;
    }
    
    /**
     * sets the time after which automatic rule application shall be aborted
     * (-1 disables timeout)
     * @param timeout a long specifying the timeout in ms
     */
    public void setTimeout(long timeout) {
        if (timeout != this.timeout) {
            this.timeout = timeout;
            fireSettingsChanged();
        }
    }

    /**
     * <p>
     * Returns the {@link StopCondition} to use in an {@link ApplyStrategy}
     * instance to determine after each applied rule if more rules
     * should be applied or not.
     * </p>
     * <p>
     * By default is an {@link AppliedRuleStopCondition} used which stops
     * the auto mode if the given maximal number of rule applications or a
     * defined timeout is reached. If a customized implementation is defined
     * for the current proof via {@link #setCustomApplyStrategyStopCondition(StopCondition)}
     * this instance is returned instead.
     * </p>
     * @return The {@link StopCondition} to use in an {@link ApplyStrategy} instance.
     */
    public StopCondition getApplyStrategyStopCondition() {
        if (customApplyStrategyStopCondition != null) {
            return customApplyStrategyStopCondition;
        }
        else {
            return new AppliedRuleStopCondition();
        }
    }

    /**
     * Returns a customized {@link StopCondition} which is used in an
     * {@link ApplyStrategy} to determine after each applied rule if more rules
     * should be applied or not.
     * @return The customized {@link StopCondition} or {@code null} if the default one should be used.
     */
    public StopCondition getCustomApplyStrategyStopCondition() {
        return customApplyStrategyStopCondition;
    }

    /**
     * Defines the {@link StopCondition} which is used in an
     * {@link ApplyStrategy} to determine after each applied rule if more rules
     * should be applied or not.
     * @param customApplyStrategyStopCondition The customized {@link StopCondition} to use or {@code null} to use the default one.
     */
    public void setCustomApplyStrategyStopCondition(StopCondition customApplyStrategyStopCondition) {
        this.customApplyStrategyStopCondition = customApplyStrategyStopCondition;
    }

    /**
     * Returns the customized {@link GoalChooser} which is used in an
     * {@link ApplyStrategy} instance to select the next {@link Goal} to
     * apply a rule on. If no one is defined the default one of the
     * {@link ApplyStrategy}, which is defined by the user interface, is used.
     * @return The customized {@link GoalChooser} to use or {@code null} to use the default one of the {@link ApplyStrategy}.
     */
    public GoalChooser getCustomApplyStrategyGoalChooser() {
        return customApplyStrategyGoalChooser;
    }

    /**
     * Sets the customized {@link GoalChooser} which is used in an
     * {@link ApplyStrategy} instance to select the next {@link Goal} to
     * apply a rule on. If no one is defined the default one of the
     * {@link ApplyStrategy}, which is defined by the user interface, is used.
     * @param customGoalChooser The customized {@link GoalChooser} to use or {@code null} to use the default one of the {@link ApplyStrategy}.
     */
    public void setCustomApplyStrategyGoalChooser(GoalChooser customGoalChooser) {
        this.customApplyStrategyGoalChooser = customGoalChooser;
    }
}