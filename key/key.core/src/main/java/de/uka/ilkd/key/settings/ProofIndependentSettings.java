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
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Date;
import java.util.LinkedList;
import java.util.List;
import java.util.Properties;

import de.uka.ilkd.key.pp.NotationInfo;


/**
 * Top of the proof independent settings.
 * <p>
 *     You can add your own settings by calling {@link #addSettings(Settings)}.
 *
 * @see Settings
 */
public class ProofIndependentSettings {
    public static final ProofIndependentSettings DEFAULT_INSTANCE =
            new ProofIndependentSettings(PathConfig.getProofIndependentSettings());
    private final ProofIndependentSMTSettings smtSettings =
            ProofIndependentSMTSettings.getDefaultSettingsData();
    private final LemmaGeneratorSettings lemmaGeneratorSettings =
            new LemmaGeneratorSettings();
    private final GeneralSettings generalSettings = new GeneralSettings();
    private final ViewSettings viewSettings = new ViewSettings();
    private final TermLabelSettings termLabelSettings = new TermLabelSettings();
    private final String filename;

    private final TestGenerationSettings testGenSettings = new TestGenerationSettings();

    private final List<Settings> settings = new LinkedList<>();

    private SettingsListener settingsListener = e -> saveSettings();
    private Properties lastReadedProperties;

    private ProofIndependentSettings(String filename) {
        addSettings(smtSettings);
        addSettings(lemmaGeneratorSettings);
        addSettings(generalSettings);
        addSettings(viewSettings);
        addSettings(testGenSettings);
        this.filename = filename;
        loadSettings();
    }

    public void addSettings(Settings settings) {
        if (!this.settings.contains(settings)) {
            this.settings.add(settings);
            settings.addSettingsListener(settingsListener);
            if (lastReadedProperties != null) {
                settings.readSettings(lastReadedProperties);
            }
        }
    }

    private void loadSettings() {
        try {
            File testFile = new File(filename);
            if(testFile.exists()) {
                if(Boolean.getBoolean(PathConfig.DISREGARD_SETTINGS_PROPERTY)) {
                    System.err.println("The settings in " + filename + " are *not* read.");
                } else {
                    load(testFile);
                }
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private void load(File file) throws IOException {
        try(FileInputStream in = new FileInputStream(file)) {
            Properties properties = new Properties();
            properties.load(in);
            for (Settings settings : settings) {
                settings.readSettings(properties);
            }
            lastReadedProperties = properties;
        }
    }

    public void saveSettings() {
        Properties result = new Properties();
        for (Settings settings : settings) {
            settings.writeSettings(result);
        }

        File file = new File(filename);
        if (!file.exists()) {
            file.getParentFile().mkdirs();
        }

        try (FileOutputStream out = new FileOutputStream(file)) {
            result.store(out, "Proof-Independent-Settings-File. Generated "+ new Date());
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public GeneralSettings getGeneralSettings() {
        return generalSettings;
    }

    public TermLabelSettings getTermLabelSettings() {
        return termLabelSettings;
    }

    public ViewSettings getViewSettings() {
        return viewSettings;
    }

    public LemmaGeneratorSettings getLemmaGeneratorSettings() {
        return lemmaGeneratorSettings;
    }

    public ProofIndependentSMTSettings getSMTSettings() {
        return smtSettings;
    }

    public TestGenerationSettings getTestGenerationSettings() {
        return testGenSettings;
    }

    /**
     * Checks if pretty printing is enabled or not.
     * @return {@code true} pretty printing is enabled, {@code false} pretty printing is disabled.
     */
    public static boolean isUsePrettyPrinting() {
        return ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUsePretty();
    }

    /**
     * Defines if pretty printing is enabled or not.
     * @param usePrettyPrinting {@code true} pretty printing is enabled,
     *     {@code false} pretty printing is disabled.
     */
    public static void setUsePrettyPrinting(boolean usePrettyPrinting) {
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setUsePretty(usePrettyPrinting);
        NotationInfo.DEFAULT_PRETTY_SYNTAX = usePrettyPrinting;
    }
}
