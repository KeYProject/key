package de.uka.ilkd.key.proof.init;

import java.util.HashMap;

import de.uka.ilkd.key.gui.IMain;
import de.uka.ilkd.key.gui.configuration.ChoiceSettings;
import de.uka.ilkd.key.gui.configuration.ProofSettings;

public class RTSJProfile extends JavaProfile {

	/**
	 *  determines whether memory consumption is taken into account in proofs or not
	 */
	private boolean memory = false;
	
    public RTSJProfile(boolean memory) {
        this(null);
        this.memory = memory;
    }
    
    public RTSJProfile(IMain main) {
        super(main);
    }
    
    public void updateSettings(ProofSettings settings) {        
        ChoiceSettings cs = settings.getChoiceSettings();
        HashMap<String, String> dcs = cs.getDefaultChoices();
        dcs.put("rtsj", "rtsj:on");
        dcs.put("perc", "perc:off");
        if(memory){
        	dcs.put("memoryConsumption", "memoryConsumption:on");
        }
        cs.setDefaultChoices(dcs);
    }
    
    public boolean memoryConsumption(){
    	return memory;
    }
    
}
