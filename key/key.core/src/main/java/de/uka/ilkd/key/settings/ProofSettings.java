// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.settings;

import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;
import java.io.StringWriter;
import java.io.Writer;
import java.net.URL;
import java.util.LinkedList;
import java.util.List;
import java.util.Properties;

import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.KeYResourceManager;

/**
 * This class is used to load and save settings for proofs such as which data
 * type models are used to represent the java types. Which heuristics have to be
 * loaded and so on. The class loads the file proofsettings.config from the
 * place where you started key. If the file is not available standard settings
 * are used. The loaded file has the following structure: <code>
 * // KeY-Configuration file
 * ActiveHeuristics=simplify_prog , simplify
 * MaximumNumberOfHeuristcsApplications=400
 * number  = IntegerLDT.class
 * boolean = BooleanLDT.class
 * </code>
 *
 * @see Properties
 * @see Settings
 */
public class ProofSettings {
    public static final File PROVER_CONFIG_FILE = new File(PathConfig.getKeyConfigDir(), "proof-settings.props");
    public static final URL PROVER_CONFIG_FILE_TEMPLATE = KeYResourceManager.getManager()
            .getResourceFile(ProofSettings.class, "default-proof-settings.props");
    public static final ProofSettings DEFAULT_SETTINGS = ProofSettings.loadedSettings();

    private static ProofSettings loadedSettings() {
        ProofSettings ps = new ProofSettings();
        ps.loadSettings();
        return ps;
    }

    /**
     * all setting objects in the following order: heuristicSettings
     */
    private List<Settings> settings = new LinkedList<>();

    /**
     * the default listener to settings
     */
    private SettingsListener listener = e -> saveSettings();

    // NOTE: This was commented out in commit
    // 4932e4d1210356455c04a1e9fb7f2fa1f21b3e9d, 2012/11/08, in the process of
    // separating proof independent from proof dependent settings.
    // Is not in ProofIndependentSettings. I don't know why these code
    // corpses have been left here as comments, therefore I don't removed them.
    // (DS, 2017-05-11)

    // private final static int strategySettings = 0;
    // private final static int GENERAL_SETTINGS = 1;
    // private final static int choiceSettings = 2;
    // private final static int smtSettings = 3;
    // private final static int VIEW_SETTINGS = 4;
    private final StrategySettings strategySettings = new StrategySettings();
    private ChoiceSettings choiceSettings = new ChoiceSettings();
    private final ProofDependentSMTSettings smtSettings = ProofDependentSMTSettings.getDefaultSettingsData();
    private Properties lastLoadedProperties = null;
    private TermLabelSettings termLabelSettings = new TermLabelSettings();

    /**
     * create a proof settings object. When you add a new settings object,
     * PLEASE UPDATE THE LIST ABOVE AND USE THOSE CONSTANTS INSTEAD OF USING
     * INTEGERS DIRECTLY
     */
    private ProofSettings() {
        addSettings(strategySettings);
        addSettings(choiceSettings);
        addSettings(smtSettings);
        addSettings(termLabelSettings);
    }

    /*
     * copy constructor - substitutes .clone() in classes implementing Settings
     */
    public ProofSettings(ProofSettings toCopy) {
        this();
        Properties result = new Properties();
        lastLoadedProperties = toCopy.lastLoadedProperties;
        for (Settings s : toCopy.settings) {
            s.writeSettings(result);
        }
        for (Settings s : settings) {
            s.readSettings(result);
        }
    }


    public void addSettings(Settings settings) {
        this.settings.add(settings);
        settings.addSettingsListener(listener);
        if (lastLoadedProperties != null) {
            settings.readSettings(lastLoadedProperties);
        }
    }

    /**
     *
     */
    public Properties getProperties() {
        Properties result = new Properties();
        for (Settings s : settings) {
            s.writeSettings(result);
        }
        return result;
    }

    /**
     * Used by saveSettings() and settingsToString()
     */
    public void settingsToStream(Writer out) {
        try {
            getProperties().store(out, "Proof-Settings-Config-File");
        } catch (IOException e) {
            System.err.println("Warning: could not save proof-settings.");
            e.printStackTrace();
            Debug.out(e);
        }
    }

    /**
     * Saves the current settings in this dialog into a configuration file.
     */
    public void saveSettings() {
        try {
            if (!PROVER_CONFIG_FILE.exists()) {
                PROVER_CONFIG_FILE.getParentFile().mkdirs();
            }
            try (Writer out = new FileWriter(PROVER_CONFIG_FILE)) {
                settingsToStream(out);
            }
        } catch (IOException e) {
            System.err.println("Warning: could not save proof-settings.");
            e.printStackTrace();
            Debug.out(e);
        }
    }

    public String settingsToString() {
        StringWriter out = new StringWriter();
        settingsToStream(out);
        return out.getBuffer().toString();
    }

    /**
     * Used by loadSettings() and loadSettingsFromString(...)
     */
    public void loadSettingsFromStream(Reader in) {
        Properties defaultProps = new Properties();

        if (PROVER_CONFIG_FILE_TEMPLATE == null) {
            System.err.println("Warning: default proof-settings file could not be found.");
        } else {
            try {
                defaultProps.load(PROVER_CONFIG_FILE_TEMPLATE.openStream());
            } catch (IOException e) {
                System.err.println("Warning: default proof-settings could not be loaded.");
                Debug.out(e);
            }
        }

        Properties props = new Properties(defaultProps);
        try {
            props.load(in);
        } catch (IOException e) {
            System.err.println("Warning: no proof-settings could be loaded, using defaults");
            Debug.out(e);
        }
        lastLoadedProperties = props;
        for (Settings s : settings) {
            s.readSettings(props);
        }
    }

    /**
     * Loads the the former settings from configuration file.
     */
    //private AtomicInteger counter = new AtomicInteger();
    public void loadSettings() {
        //System.out.println("ProofSettings.loadSettings:" + counter.getAndIncrement());
        try (FileReader in = new FileReader(PROVER_CONFIG_FILE)) {
            if (Boolean.getBoolean(PathConfig.DISREGARD_SETTINGS_PROPERTY)) {
                System.err.println("The settings in " + PROVER_CONFIG_FILE + " are *not* read.");
            } else {
                loadSettingsFromStream(in);
            }
        } catch (IOException e) {
            System.err.println(
                    "Warning: no proof-settings could be loaded, using defaults");
            Debug.out(e);
        }
    }

    /**
     * Used to load Settings from a .key file
     */
    public void loadSettingsFromString(String s) {
        if (s == null) {
            return;
        }
        StringReader reader = new StringReader(s);
        loadSettingsFromStream(reader);
    }

    /**
     * returns the StrategySettings object
     *
     * @return the StrategySettings object
     */
    public StrategySettings getStrategySettings() {
        return strategySettings;
    }

    /**
     * returns the ChoiceSettings object
     *
     * @return the ChoiceSettings object
     */
    public ChoiceSettings getChoiceSettings() {
        return choiceSettings;
    }

    /**
     * returns the DecisionProcedureSettings object
     *
     * @return the DecisionProcedureSettings object
     */
    public ProofDependentSMTSettings getSMTSettings() {
        return smtSettings;
    }

    /**
     * Checks if the choice settings are initialized.
     *
     * @return {@code true} settings are initialized, {@code false} settings are
     * not initialized.
     */
    public static boolean isChoiceSettingInitialised() {
        return !ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getChoices()
                .isEmpty();
    }

    /**
     * Update the proof settings according to the entries on the properties.
     *
     * @param props a non-<code>null</code> object with KeY properties.
     */
    public void update(Properties props) {
        for (Settings s : settings) {
            s.readSettings(props);
        }
    }


    /**
     * Returns the term label settings from the proof settings.
     * @return the term label settings
     */
    public TermLabelSettings getTermLabelSettings() {
        return termLabelSettings;
    }
}
