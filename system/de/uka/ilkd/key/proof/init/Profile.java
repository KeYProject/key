package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.collection.SetOfString;
import de.uka.ilkd.key.gui.ProofSettings;
import de.uka.ilkd.key.lang.common.services.ILangServices;
import de.uka.ilkd.key.lang.common.services.ILangServicesEnv;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.GoalChooserBuilder;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.strategy.SetOfStrategyFactory;
import de.uka.ilkd.key.strategy.StrategyFactory;

/**
 * 
 * This interface provides methods that allow to customize KeY for
 * certain applications. It supports to customize
 * <ul>
 * <li> the rule base to be used </li>
 * <li> the available strategies </li>
 * <li> the goal selection strategy </li>
 * </ul> 
 * 
 * Currently this is only rudimentary: possible extensions are 
 *    <ul>
 *    <li> program model to use (java, misrac, csharp) </li>
 *    <li> integrate in plug-in framework allow addition of menu entries
 *         toolbar buttons etc.
 *    </li>
 *    </ul>
 * etc.
 */
public interface Profile {
    
    /** returns the rule source containg all taclets for this profile */
    RuleCollection getStandardRules();
       
    /** the name of this profile */
    String name();

    /** returns the strategy factories for the supported strategies */
    SetOfStrategyFactory supportedStrategies();
    
    /** 
     * returns the strategy factory for the default strategy of this profile 
     */
    StrategyFactory getDefaultStrategyFactory();

    /** 
     * returns true if strategy <code>strategyName</code> may be 
     * used with this profile.      
     * @return supportedStrategies()->exists(s | s.name.equals(strategyName))
     */
    boolean supportsStrategyFactory(Name strategyName);

    /**
     * returns the StrategyFactory for strategy <code>strategyName</code>
     * @param strategyName the Name of the strategy
     * @return the StrategyFactory to build the demanded strategy
     */
    StrategyFactory getStrategyFactory(Name strategyName);

   /**
    * returns the names of possible goalchoosers to be used by the 
    * automatic prover environment
    */
    SetOfString supportedGoalChoosers();
 
    /** 
     * returns the default builder for a goal chooser      
     */
    GoalChooserBuilder getDefaultGoalChooserBuilder();
    
    /**
     * sets the user selected goal chooser builder to be used as prototype
     * @param name the String with the name of the goal chooser to be used
     * @throws IllegalArgumentException if a goal chooser of the given name is not
      *  supported
     */
    void setSelectedGoalChooserBuilder(String name);
    
    /**
     * returns a new builder instance for the selected goal choooser 
     */
    GoalChooserBuilder getSelectedGoalChooserBuilder();

    /** returns the (default) justification for the given rule */
    RuleJustification getJustification(Rule r);

    /** 
     * 
     * @param settings the ProofSettings to be updated to defaults provided by 
     * this profile
     */
    void updateSettings(ProofSettings settings);
    
    /**
     * Returns an fresh instance of language services for this profile, may be <code>null</code>.
     * @param env language services environment to use
     * @return
     * @author oleg.myrk@gmail.com
     */
    ILangServices getLanguageServices(ILangServicesEnv env);    
}
