// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.Properties;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.strategy.SimpleJavaCardDLOptions;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.Debug;



public class StrategySettings implements Settings {

    private static final String STRATEGY_KEY = "[Strategy]ActiveStrategy";
    private static final String STEPS_KEY = "[Strategy]MaximumNumberOfAutomaticApplications";
    private static final String TIMEOUT_KEY = "[Strategy]Timeout";
    
    private LinkedList listenerList = new LinkedList();
    
    private Name activeStrategy;

    /** maximal number of automatic rule applications before an interaction is required */ 
    private int maxSteps = -1;
    
    /** maximal time in ms after which automatic rule application is aborted */
    private long timeout = -1;
    
    private StrategyProperties strategyProperties = new StrategyProperties();
    
    /** returns the maximal amount of heuristics steps before an user
     * interaction is required 
     * @return the maximal amount of heuristics steps before an user
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
    public void readSettings ( Properties props ) {
        String numString = props.getProperty(STEPS_KEY);
        String strategyString = props.getProperty(STRATEGY_KEY);
        String timeoutString = props.getProperty(TIMEOUT_KEY);
    
        long localTimeout = -1;
        int numSteps = 1000;
    
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
    public void writeSettings ( Properties props ) {
	if (getStrategy()==null) {
	    setStrategy(SimpleJavaCardDLOptions.LOOPS_METHODS.name());
	}
	if (maxSteps<0) {
	    setMaxSteps(1000);
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
        Iterator it = listenerList.iterator();
        while (it.hasNext()) {
            ((SettingsListener)it.next()).settingsChanged(new GUIEvent(this));
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
}
