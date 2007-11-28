// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.gui.configuration;

import java.io.*;
import java.net.URL;
import java.util.*;

import de.uka.ilkd.key.gui.DecisionProcedureSettings;
import de.uka.ilkd.key.gui.GUIEvent;
import de.uka.ilkd.key.gui.ModelSourceSettings;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.KeYResourceManager;

/** This class is used to load and save settings for proofs such as
 * which data type models are used to represent the java types. Which
 * heuristics have to be loaded and so on.
 * The class loads the file proofsettings.config from the place where
 * you started key. If the file is not available standard settings are
 * used.
 * The loaded file has the following structure:
 * <code>
 * // KeY-Configuration file
 * ActiveHeuristics=simplify_prog , simplify
 * MaximumNumberOfHeuristcsApplications=400
 * number  = IntegerLDT.class 
 * boolean = BooleanLDT.class
 * </code>
 */
public class ProofSettings {


    public static final File PROVER_CONFIG_FILE;
    public static final URL PROVER_CONFIG_FILE_TEMPLATE;
    public static final ProofSettings DEFAULT_SETTINGS;

    static {
	PROVER_CONFIG_FILE = new File
	    (System.getProperty("user.home")+
	     File.separator+".key"+File.separator+"proof-settings.props");
	PROVER_CONFIG_FILE_TEMPLATE =
	    KeYResourceManager.getManager ().getResourceFile
	    ( ProofSettings.class, "default-proof-settings.props" );
	DEFAULT_SETTINGS = new ProofSettings();
    }

    private boolean initialized=false;


    /** all setting objects in the following order: heuristicSettings */
    private Settings[] settings;

    /** the default listener to settings */
    private ProofSettingsListener listener = new ProofSettingsListener();

    
    /** profile */
    private Profile profile;

    /** create a proof settings object */
    public ProofSettings() {       	
	settings = new Settings[] {
            new StrategySettings(),
	    new ModelSourceSettings(),
	    new SimultaneousUpdateSimplifierSettings(),
            new GeneralSettings(),
	    new ChoiceSettings(),
	    new DecisionProcedureSettings(),
	    new ViewSettings(),
            new LibrariesSettings()
	};
	for (int i = 0; i < settings.length; i++) { 
	    settings[i].addSettingsListener(listener);
	}        
    }
    
    /* copy constructor - substitutes .clone() in classes implementing Settings */
    public ProofSettings(ProofSettings toCopy) {
        this();

        Properties result = new Properties();
        Settings[] s = toCopy.settings;

        for (int i = 0; i < s.length; i++) {
            s[i].writeSettings(result);
        }
        
        for (int i = settings.length - 1; i >= 0; i--) {
            settings[i].readSettings(result);
        }
        initialized = true;
        setProfile(toCopy.getProfile());
    }

   
    public void ensureInitialized() {
	if (!initialized) {
	    loadSettings();
	    initialized=true;	
	}
    }
    
    
    public void setProfile(Profile profile) {
        ensureInitialized();
        this.profile = profile;
    }

    public Profile getProfile() {                
        if (profile == null) {
            //the following line should be removed
            profile = new JavaProfile();
        }
        return profile;
    }
    
    /** 
     * Used by saveSettings() and settingsToString()
     */
    public void settingsToStream(Settings[] s,OutputStream out) {
    try {
        Properties result = new Properties();
	    for (int i = 0; i < s.length; i++) {
	    s[i].writeSettings(result);
	    }
	    result.store(out, "Proof-Settings-Config-File");
	} catch (IOException e){
	    System.err.println("Warning: could not save proof-settings.");
	    System.err.println(e);
	    Debug.out(e);
	}
    }
    /**
     * Saves the current settings in this dialog into a configuration file.
     */
    public void saveSettings() {
	try {
	    if (!PROVER_CONFIG_FILE.exists()) {
		new File(System.getProperty("user.home")+File.separator
			 +".key"+File.separator).mkdir();
	    }
	    FileOutputStream out = 
		new FileOutputStream(PROVER_CONFIG_FILE);
	    settingsToStream(settings,out);
	} catch (IOException e){
	    System.err.println("Warning: could not save proof-settings.");
	    System.err.println(e);
	    Debug.out(e);
	}
    }

	public String settingsToString() {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        settingsToStream(settings,out);
        return new String(out.toByteArray());
    }

	/** Used by loadSettings() and loadSettingsFromString(...) */
	public void loadSettingsFromStream(InputStream in) {
	    Properties defaultProps = new Properties ();

	    if ( PROVER_CONFIG_FILE_TEMPLATE == null )
	        System.err.println
	        ("Warning: default proof-settings file could not be found.");
	    else {
	        try {
	            defaultProps.load ( PROVER_CONFIG_FILE_TEMPLATE.openStream () );
	        } catch (IOException e){
	            System.err.println
	            ("Warning: default proof-settings could not be loaded.");
	            Debug.out(e);
	        }
	    }

	    Properties props = new Properties ( defaultProps );
	    try {            
	        props.load(in);
	    } catch (IOException e){
	        System.err.println
	        ("Warning: no proof-settings could be loaded, using defaults");
	        Debug.out(e);
	    }

	    for (int i = settings.length-1; i>=0 ;i--) { 
	        settings[i].readSettings(props); 
	    }

	    initialized = true;
	}

    /**
     * Loads the the former settings from configuration file.
     */
    public void loadSettings(){
	try {
	    FileInputStream in = new FileInputStream(PROVER_CONFIG_FILE);
	    loadSettingsFromStream(in);
	} catch (IOException e){
            System.err.println
		("Warning: no proof-settings could be loaded, using defaults");
	    Debug.out(e);
	}
    }

    /** Used to load Settings from a .key file*/
    public void loadSettingsFromString(String s) {
        if (s == null) return;      
        StringBufferInputStream in = new StringBufferInputStream(s);
        loadSettingsFromStream(in);
    }

    /** returns the StrategySettings object
     * @return the StrategySettings object
     */
    public StrategySettings getStrategySettings() {
        ensureInitialized();
        return (StrategySettings) settings[0];
    }

    /** returns the ChoiceSettings object
     * @return the ChoiceSettings object
     */
    public ChoiceSettings getChoiceSettings() {
	ensureInitialized();
	return (ChoiceSettings) settings[4];
    }

    public ProofSettings setChoiceSettings(ChoiceSettings cs) {
	settings[4] = cs;
        return this;
    }

    /** returns the DecisionProcedureSettings object
     * @return the DecisionProcedureSettings object
     */
    public DecisionProcedureSettings getDecisionProcedureSettings() {
	ensureInitialized();
	return (DecisionProcedureSettings) settings[5];
    }

    public ModelSourceSettings getModelSourceSettings() {
	ensureInitialized();
	return (ModelSourceSettings) settings[1];
    }

    public SimultaneousUpdateSimplifierSettings 
	getSimultaneousUpdateSimplifierSettings() {
	ensureInitialized();
	return (SimultaneousUpdateSimplifierSettings) settings[2];    
    }
    
    public LibrariesSettings getLibrariesSettings() {
        ensureInitialized();
        return (LibrariesSettings) settings[7];    
    }

    public GeneralSettings getGeneralSettings() {
	ensureInitialized();
	return (GeneralSettings) settings[3];
    }

    public ViewSettings getViewSettings() {
	ensureInitialized();
	return (ViewSettings) settings[6];
    }

    private class ProofSettingsListener implements SettingsListener {
	
	ProofSettingsListener() {
	}

	/** called by the Settings object to inform the listener that its
	 * state has changed
	 * @param e the Event sent to the listener
	 */
	public void settingsChanged(GUIEvent e) {	    
	    saveSettings();
	}

    }
    
}
