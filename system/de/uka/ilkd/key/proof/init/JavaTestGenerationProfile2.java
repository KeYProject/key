// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.proof.init;

import java.util.HashMap;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.IMain;
import de.uka.ilkd.key.gui.configuration.ChoiceSettings;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.BalancedGoalChooserBuilder;
import de.uka.ilkd.key.rule.metaconstruct.WhileLoopTransformation2;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.VBTStrategy;


/** This profile is for verification-based testing. The rule set standardRules-testGen2.key is loaded.
 * In contrast to {@link de.uka.ilkd.key.proof.init.JavaTestGenerationProfile}, this
 * modus is closer to the normal mode of KeY respecting the rule sets and proof strategy.
 * @author gladisch
 * */
public class JavaTestGenerationProfile2 extends JavaProfile {

    
    private final static StrategyFactory DEFAULT =
        new VBTStrategy.Factory(1);

    public JavaTestGenerationProfile2(IMain main) {
        super("standardRules-testGen2.key",  main);
    }
    
    /** @param main can be null. It is not used
     *  @param loop - if true then the BalancedGoalChooserBuilder is selected. This parameter is independent from @param loopBound.
     *  @param loopBound - if the value is smaller than 0 then it has no effect (unbounded loop unwinding is used). 
     *  Otherwise if @loopBound is equal or greater than 0 then this is the number of loop iterations considered. 
     */
    public JavaTestGenerationProfile2(IMain main, boolean loop, int loopBound ) {
	this(main);
	if(loop){
	    VBTStrategy.preferedGoalChooser = BalancedGoalChooserBuilder.NAME;
	    setSelectedGoalChooserBuilder(VBTStrategy.preferedGoalChooser);
	}
	if(loopBound>=0){
            VBTStrategy.loopUnwindBounded = true;
            WhileLoopTransformation2.unwindings=loopBound;
	}
    }

    protected ImmutableSet<StrategyFactory> getStrategyFactories() {
        return
            super.getStrategyFactories().add(DEFAULT);
    }

    public String name() {
        return "Java Verification + Test Case Generation Profile 2";
    }

    public StrategyFactory getDefaultStrategyFactory() {
        return DEFAULT;
    }

    public void updateSettings(ProofSettings settings) {
        ChoiceSettings cs = settings.getChoiceSettings();
        HashMap<String, String> dcs = cs.getDefaultChoices();
        dcs.put("testGeneration", "testGeneration:testOn");
        cs.setDefaultChoices(dcs);
        settings.getStrategySettings().setStrategy(new Name("VBTStrategy"));
        super.updateSettings(settings);
    }

}
