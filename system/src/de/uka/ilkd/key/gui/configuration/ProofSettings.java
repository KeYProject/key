// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.gui.configuration;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.StringBufferInputStream;
import java.net.URL;
import java.util.Properties;

import de.uka.ilkd.key.gui.GUIEvent;
import de.uka.ilkd.key.gui.smt.ProofDependentSMTSettings;
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
	    (PathConfig.getKeyConfigDir()+File.separator+"proof-settings.props");
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

//    private final static int STRATEGY_SETTINGS = 0;
//    private final static int GENERAL_SETTINGS  = 1;
//    private final static int CHOICE_SETTINGS    = 2;
//    private final static int SMT_SETTINGS      = 3;
//    private final static int VIEW_SETTINGS      = 4;
    private final static int STRATEGY_SETTINGS = 0;
    private final static int CHOICE_SETTINGS   = 1;
    private final static int SMT_SETTINGS      = 2;
    private final static int LABEL_SETTINGS    = 3;

    
    /** create a proof settings object. 
     * When you add a new settings object, PLEASE UPDATE 
     * THE LIST ABOVE AND USE THOSE CONSTANTS INSTEAD OF USING INTEGERS DIRECTLY */
 
    private ProofSettings() {       	
	settings = new Settings[] {
            new StrategySettings(),
          //  new GeneralSettings(),
	    new ChoiceSettings(),
	    ProofDependentSMTSettings.getDefaultSettingsData(),
	 //   new ViewSettings()
       new LabelSettings()
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
            s[i].writeSettings(this,result);
        }
        
        for (int i = settings.length - 1; i >= 0; i--) {
            settings[i].readSettings(this,result);
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
        this.profile = profile;
        profile.updateSettings(this);
        ensureInitialized();
    }

    public Profile getProfile() {                
        if (profile == null) {
            //the following line should be removed
            setProfile(new JavaProfile());
            
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
	    s[i].writeSettings(this,result);
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
	ensureInitialized();
	try {
	    if (!PROVER_CONFIG_FILE.exists()) {	                       
                new File(PathConfig.getKeyConfigDir()+File.separator).mkdirs();
                PROVER_CONFIG_FILE.createNewFile();
	    }            
	    FileOutputStream out = 
		new FileOutputStream(PROVER_CONFIG_FILE);
	    try { 
	        settingsToStream(settings,out);
	    } finally {
	        out.close();
	    }
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
	        settings[i].readSettings(this,props); 
	    }

	    initialized = true;
	}

    /**
     * Loads the the former settings from configuration file.
     */
    public void loadSettings(){
	try {
	    FileInputStream in = new FileInputStream(PROVER_CONFIG_FILE);
	    try { 
	        loadSettingsFromStream(in);
	    } finally {
	        in.close();
	    }
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
        return (StrategySettings) settings[STRATEGY_SETTINGS];
    }

    /**
     * Returns the {@link LabelSettings}.
     * @return The {@link LabelSettings}.
     */
    public LabelSettings getLabelSettings() {
        ensureInitialized();
        return (LabelSettings) settings[LABEL_SETTINGS];
    }

    /** returns the ChoiceSettings object
     * @return the ChoiceSettings object
     */
    public ChoiceSettings getChoiceSettings() {
            ensureInitialized();
            return (ChoiceSettings) settings[CHOICE_SETTINGS];
    }

    public ProofSettings setChoiceSettings(ChoiceSettings cs) {
            settings[CHOICE_SETTINGS] = cs;
            return this;
    }

    /** returns the DecisionProcedureSettings object
     * @return the DecisionProcedureSettings object
     */
    public ProofDependentSMTSettings getSMTSettings() {
            ensureInitialized();
            return (ProofDependentSMTSettings) settings[SMT_SETTINGS];
    }
    

//
//
//    public GeneralSettings getGeneralSettings() {
//            ensureInitialized();
//            return (GeneralSettings) settings[GENERAL_SETTINGS];
//    }
//
//    public ViewSettings getViewSettings() {
//            ensureInitialized();
//            return (ViewSettings) settings[VIEW_SETTINGS];
//    }

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
