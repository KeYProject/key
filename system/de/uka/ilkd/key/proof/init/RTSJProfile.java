package de.uka.ilkd.key.proof.init;

import java.util.HashMap;

import de.uka.ilkd.key.gui.IMain;
import de.uka.ilkd.key.gui.POBrowser;
import de.uka.ilkd.key.gui.configuration.ChoiceSettings;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.proof.init.proofobligation.DefaultPOProvider;
import de.uka.ilkd.key.rtsj.proof.init.proofobligation.RTSJPOProvider;

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
        super("standardRules-RTSJ.key", main);
    }
    
    public void updateSettings(ProofSettings settings) {        
        ChoiceSettings cs = settings.getChoiceSettings();
        HashMap<String, String> dcs = cs.getDefaultChoices();
        dcs.put("rtsj", "rtsj:on");
        if(memory){
	    dcs.put("memory", "memory:on");
        }else{
	    dcs.put("memory", "memory:off");
	}
        cs.setDefaultChoices(dcs);
    }
    
    
    /**
     * the name of the profile
     */
    public String name() {
        return "Realtime Java (RTSJ) Profile";
    }
    
    public boolean memoryConsumption(){
    	return memory;
    }
    
    /**
     * returns the file name of the internal class directory relative to JavaRedux
     * @return the file name of the internal class directory relative to JavaRedux
     */
    public String getInternalClassDirectory() {
	return "rtsjperc";
    }
    
    /**
     * returns the file name of the internal class list
     * @return the file name of the internal class list
     */
    public String getInternalClasslistFilename() {
	 return "JAVALANGRTSJ.TXT";
    }
    
    public DefaultPOProvider getPOProvider() {
	return new RTSJPOProvider(memory);
    }
    
    public Class<? extends POBrowser> getPOBrowserClass() {
	return de.uka.ilkd.key.rtsj.gui.POBrowserRTSJ.class;
    }

}
