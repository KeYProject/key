package de.uka.ilkd.key.proof.init;

import java.util.HashMap;

import de.uka.ilkd.key.gui.IMain;
import de.uka.ilkd.key.gui.configuration.ChoiceSettings;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.BalancedGoalChooserBuilder;
import de.uka.ilkd.key.proof.DefaultGoalChooserBuilder;
import de.uka.ilkd.key.proof.SetAsListOfGoalChooserBuilder;
import de.uka.ilkd.key.strategy.SetOfStrategyFactory;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.VBTStrategy;

public class JavaTestGenerationProfile extends JavaProfile {
   
    private final static StrategyFactory DEFAULT = 
        new VBTStrategy.Factory();
    
    public JavaTestGenerationProfile(IMain main) {
        super("standardRules-testGen.key", 
                SetAsListOfGoalChooserBuilder.EMPTY_SET.
                add(new DefaultGoalChooserBuilder()).
                add(new BalancedGoalChooserBuilder()),                 
                main);        
    }
       
    protected SetOfStrategyFactory getStrategyFactories() {
        return
            super.getStrategyFactories().add(DEFAULT);
    }
          
    public String name() {
        return "Java Testcase Generation Profile";
    }
  
    public StrategyFactory getDefaultStrategyFactory() {
        return DEFAULT;
    }      
    
    public void updateSettings(ProofSettings settings) {        
        ChoiceSettings cs = settings.getChoiceSettings();
        HashMap dcs = cs.getDefaultChoices();
        dcs.put("testGeneration", "testGeneration:testOn");
        cs.setDefaultChoices(dcs);
        settings.getStrategySettings().setStrategy(new Name("VBTStrategy"));        
    }
    
}
