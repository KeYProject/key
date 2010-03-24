package de.uka.ilkd.key.proof.init;

import java.util.HashMap;

import de.uka.ilkd.key.gui.IMain;
import de.uka.ilkd.key.gui.configuration.ChoiceSettings;
import de.uka.ilkd.key.gui.configuration.ProofSettings;

public class PercProfile extends JavaProfile {

    
    public PercProfile() {
        this(null);
    }
    
    public PercProfile(IMain main) {
        super(main);
    }
    
    public void updateSettings(ProofSettings settings) {        
        ChoiceSettings cs = settings.getChoiceSettings();
        HashMap<String, String> dcs = cs.getDefaultChoices();
        dcs.put("rtsj", "rtsj:off");
        dcs.put("perc", "perc:on");
        cs.setDefaultChoices(dcs);
    }
    
}