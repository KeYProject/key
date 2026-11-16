/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.settings;

import java.beans.PropertyChangeListener;
import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.*;

import de.uka.ilkd.key.pp.NotationInfo;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


/**
 * Top of the proof independent settings.
 * <p>
 * You can add your own settings by calling {@link #addSettings(Settings)}.
 *
 * @see Settings
 */
@NullMarked
public class ProofIndependentSettings {
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofIndependentSettings.class);

    public static final ProofIndependentSettings DEFAULT_INSTANCE;

    static {
        var write = Objects.requireNonNull(PathConfig.currentPaths,
            "KeY paths are not initialized").proofIndependentSettings;
        var read = Objects.requireNonNull(PathConfig.previousPaths,
            "KeY paths are not initialized").proofIndependentSettings;

        if (Files.exists(write)) {
            read = write;
        }

        // change to props file, if json file does not exists
        if (!Files.exists(read)) {
            // the file name is guaranteed present: a root path has no parent, so the
            // requireNonNull below would throw first; fall back to the (non-null) path itself
            var settingsFileName = read.getFileName();
            read = Objects.requireNonNull(read.getParent(),
                "settings file has no parent directory").resolve(
                    (settingsFileName != null ? settingsFileName : read).toString()
                            .replace(".json", ".props"));
        }

        // read from the old/new place
        DEFAULT_INSTANCE = new ProofIndependentSettings(read.toFile());

        // set the write place
        DEFAULT_INSTANCE.filename = write.toFile();
    }

    private final ProofIndependentSMTSettings smtSettings =
        ProofIndependentSMTSettings.getDefaultSettingsData();

    private final LemmaGeneratorSettings lemmaGeneratorSettings = new LemmaGeneratorSettings();
    private final GeneralSettings generalSettings = new GeneralSettings();
    private final ViewSettings viewSettings = new ViewSettings();
    private final TermLabelSettings termLabelSettings = new TermLabelSettings();
    private final FeatureSettings featureSettings = new FeatureSettings();
    private final StrategyPresetsSettings strategyPresetsSettings = new StrategyPresetsSettings();

    // always overwritten before any use (in the ProofIndependentSettings(File)
    // constructor or the static initializer), so the default value is never observed
    private File filename = new File("");


    private final List<Settings> settings = new LinkedList<>();

    /**
     * The listener lambda calls {@link #saveSettings()} on {@code this} while the receiver is
     * still being constructed (EISOP initialization check); safe here because the listener only
     * fires on later property-change events, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    private final PropertyChangeListener settingsListener = e -> saveSettings();
    private @Nullable Properties lastReadProperties;
    private @Nullable Configuration lastReadConfiguration;

    /**
     * The settings registrations operate on {@code this} while the receiver is still under
     * initialization (EISOP initialization check); safe here because each settings object is
     * fully constructed before registration, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    private ProofIndependentSettings() {
        addSettings(smtSettings);
        addSettings(lemmaGeneratorSettings);
        addSettings(generalSettings);
        addSettings(viewSettings);
        addSettings(featureSettings);
        addSettings(strategyPresetsSettings);
    }

    /**
     * The settings persistence is reloaded while the receiver is still under initialization
     * (EISOP initialization check); the registered settings objects are all complete, so the
     * difference is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    private ProofIndependentSettings(File filename) {
        this();
        this.filename = filename;
        loadSettings();
    }

    public void addSettings(Settings settings) {
        if (!this.settings.contains(settings)) {
            this.settings.add(settings);
            settings.addPropertyChangeListener(settingsListener);
            if (lastReadProperties != null) {
                settings.readSettings(lastReadProperties);
            }
            if (lastReadConfiguration != null) {
                settings.readSettings(lastReadConfiguration);
            }
        }
    }

    private void loadSettings() {
        try {
            if (filename.exists()) {
                if (PathConfig.DISREGARD_SETTINGS) {
                    LOGGER.warn("The settings in {} are *not* read due to flag '{}'", filename,
                        PathConfig.DISREGARD_SETTINGS_PROPERTY);
                } else {
                    load(filename);
                }
            }
        } catch (Exception e) {
            LOGGER.error("Could not load settings from {}", filename, e);
        }
    }

    private void load(File file) throws IOException {
        if (!file.getName().endsWith(".json")) {
            try (FileInputStream in = new FileInputStream(file)) {
                Properties properties = new Properties();
                properties.load(in);
                for (Settings settings : settings) {
                    settings.readSettings(properties);
                }
                lastReadProperties = properties;
            }
        } else {
            Configuration config = Configuration.load(file.toPath());
            this.lastReadConfiguration = config;
            for (Settings settings : settings) {
                settings.readSettings(config);
            }
        }
    }

    /**
     * Writes the properties and configuration of all registered settings to the settings file.
     * <p>
     * The settings file is created at its configured location, whose parent directory always
     * exists by then; the dereferences of the (nullable) parent of the filename are suppressed
     * with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    public void saveSettings() {
        if (!filename.getName().endsWith(".json")) {
            Properties result = lastReadProperties == null
                    ? new Properties()
                    : new Properties(lastReadProperties);

            for (Settings settings : settings) {
                settings.writeSettings(result);
            }

            if (!filename.exists()) {
                filename.getParentFile().mkdirs();
            }

            try (var out = new FileOutputStream(filename)) {
                result.store(out, "Proof-Independent-Settings-File. Generated " + new Date());
            } catch (IOException e) {
                LOGGER.error("Could not store settings to {}", filename, e);
            }
        }

        Configuration config = new Configuration();
        if (lastReadConfiguration != null) {
            config.overwriteWith(lastReadConfiguration);
        }

        for (var settings : settings)
            settings.writeSettings(config);
        if (!filename.exists()) {
            filename.getParentFile().mkdirs();
        }

        try (var out = new BufferedWriter(new FileWriter(
            filename.toString().replace(".props", ".json"), StandardCharsets.UTF_8))) {
            config.save(out, "Proof-Independent-Settings-File. Generated " + new Date());
        } catch (IOException e) {
            LOGGER.error("Could not store settings to {}", filename, e);
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

    public FeatureSettings getFeatureSettings() {
        return featureSettings;
    }

    public StrategyPresetsSettings getStrategyPresetsSettings() {
        return strategyPresetsSettings;
    }

    /**
     * Checks if pretty printing is enabled or not.
     *
     * @return {@code true} pretty printing is enabled, {@code false} pretty printing is disabled.
     */
    public static boolean isUsePrettyPrinting() {
        return DEFAULT_INSTANCE.getViewSettings().isUsePretty();
    }

    /**
     * Defines if pretty printing is enabled or not.
     *
     * @param usePrettyPrinting {@code true} pretty printing is enabled, {@code false} pretty
     *        printing is disabled.
     */
    public static void setUsePrettyPrinting(boolean usePrettyPrinting) {
        DEFAULT_INSTANCE.getViewSettings().setUsePretty(usePrettyPrinting);
        NotationInfo.DEFAULT_PRETTY_SYNTAX = usePrettyPrinting;
    }

    /// Returns the current proof settings as a configuration object
    public Configuration asConfiguration() {
        Configuration result = new Configuration();
        for (Settings s : settings) {
            s.writeSettings(result);
        }
        return result;
    }
}
