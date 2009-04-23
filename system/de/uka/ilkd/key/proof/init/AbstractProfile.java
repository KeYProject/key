// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.collection.SetAsListOfString;
import de.uka.ilkd.key.collection.SetOfString;
import de.uka.ilkd.key.gui.IMain;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.rule.ListOfBuiltInRule;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.SLListOfBuiltInRule;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.strategy.IteratorOfStrategyFactory;
import de.uka.ilkd.key.strategy.SetAsListOfStrategyFactory;
import de.uka.ilkd.key.strategy.SetOfStrategyFactory;
import de.uka.ilkd.key.strategy.StrategyFactory;

public abstract class AbstractProfile implements Profile {

    private final RuleCollection       standardRules;

    private final SetOfStrategyFactory strategies;

    private final SetOfString supportedGC;
    private final SetOfGoalChooserBuilder supportedGCB;
    
    private GoalChooserBuilder prototype;
            
    protected AbstractProfile(String standardRuleFilename, 
            SetOfGoalChooserBuilder supportedGCB, IMain main) {
        
        standardRules = new RuleCollection(RuleSource
                .initRuleFile(standardRuleFilename), 
                initBuiltInRules());
        strategies = getStrategyFactories();
        this.supportedGCB = supportedGCB;        
        this.supportedGC = extractNames(supportedGCB);
        this.prototype = getDefaultGoalChooserBuilder();
        assert( this.prototype!=null );
        
    }

    private static 
        SetOfString extractNames(SetOfGoalChooserBuilder supportedGCB) {

        SetOfString result = SetAsListOfString.EMPTY_SET;
        
        final IteratorOfGoalChooserBuilder it = supportedGCB.iterator();
        while (it.hasNext()) {
            result  = result.add(it.next().name());
        }
        
        return result;
    }

    public AbstractProfile(String standardRuleFilename) {
        this(standardRuleFilename, null);
    }

    public AbstractProfile(String standardRuleFilename, IMain main) {
        this(standardRuleFilename, 
                SetAsListOfGoalChooserBuilder.EMPTY_SET.
                add(new DefaultGoalChooserBuilder()).
                add(new DepthFirstGoalChooserBuilder()), main);
    }

    public RuleCollection getStandardRules() {
        return standardRules;
    }

    protected SetOfStrategyFactory getStrategyFactories() {
        return SetAsListOfStrategyFactory.EMPTY_SET;
    }

    protected ListOfBuiltInRule initBuiltInRules() {
        ListOfBuiltInRule builtInRules = SLListOfBuiltInRule.EMPTY_LIST;
        
        builtInRules = builtInRules.prepend(new SMTRule(new Z3Solver()));        
        builtInRules = builtInRules.prepend(new SMTRule(new YicesSolver()));
        builtInRules = builtInRules.prepend(new SMTRule(new SimplifySolver()));        
        builtInRules = builtInRules.prepend(new SMTRule(new CVC3Solver()));
        
        return builtInRules;
    }
    

    public SetOfStrategyFactory supportedStrategies() {
        return strategies;
    }

    public boolean supportsStrategyFactory(Name strategy) {
        return getStrategyFactory(strategy) != null;
    }
    
    public StrategyFactory getStrategyFactory(Name n) {
        IteratorOfStrategyFactory it = getStrategyFactories().iterator();
        while (it.hasNext()) {
            final StrategyFactory sf = it.next();
            if (sf.name().equals(n)) {
                return sf;
            }            
        }
        return null;
    }

    /**
     * returns the names of the supported goal chooser 
     * builders
     */
     public SetOfString supportedGoalChoosers() {
         return supportedGC;
     }
  
     /** 
      * returns the default builder for a goal chooser
      * @return this implementation returns a new instance of
      * {@link DefaultGoalChooserBuilder}       
      */
     public GoalChooserBuilder getDefaultGoalChooserBuilder() {
         return new DefaultGoalChooserBuilder();
     }
               
     /**
      * sets the user selected goal chooser builder to be used as prototype
      * @throws IllegalArgumentException if a goal chooser of the given name is not
      *  supported
      */
     public void setSelectedGoalChooserBuilder(String name) {         
         
         this.prototype = lookupGC(name);
         
         if (this.prototype == null) {
             throw new IllegalArgumentException("Goal chooser:" + name +
                     " is not supported by this profile.");
         }
     }
     
     /**
      * looks up the demanded goal chooser is supported and returns a 
      * new instance if possible otherwise <code>null</code> is returned 
      *  
      * @param name the String with the goal choosers name
      * @return a new instance of the builder or <code>null</code> if the
      * demanded chooser is not supported
      */
     public GoalChooserBuilder lookupGC(String name) {
        final IteratorOfGoalChooserBuilder it  = supportedGCB.iterator();
        while (it.hasNext()) {
            final GoalChooserBuilder supprotedGCB = it.next();
            if (supprotedGCB.name().equals(name)) {
                return supprotedGCB.copy();
            }
        }
        return null;
    }

    /**
      * returns a copy of the selected goal chooser builder 
      */
     public GoalChooserBuilder getSelectedGoalChooserBuilder(){
        return prototype.copy(); 
     }
    
     /**
      * any standard rule has is by default justified by an axiom rule 
      * justification 
      * @return the justification for the standard rules             
      */
     public RuleJustification getJustification(Rule r) {
         return AxiomJustification.INSTANCE;
     }

     /**
      * sets the given settings to some default depending on the profile
      */
     public void updateSettings(ProofSettings settings) {
	 settings.getDecisionProcedureSettings().updateSMTRules(this);	 
     }   
}
