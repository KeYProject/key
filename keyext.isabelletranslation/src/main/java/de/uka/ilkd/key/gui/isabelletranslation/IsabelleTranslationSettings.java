/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.isabelletranslation;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.nio.file.Path;
import java.util.Properties;

import de.uka.ilkd.key.settings.AbstractSettings;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.settings.PathConfig;

import org.jspecify.annotations.NonNull;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class IsabelleTranslationSettings extends AbstractSettings {
    protected static final File SETTINGS_FILE_NEW =
            new File(PathConfig.getKeyConfigDir(), "isabelleSettings.json");
    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleTranslationSettings.class);
    private static IsabelleTranslationSettings INSTANCE;

    private static final String isabellePathKey = "Path";
    private static final String translationPathKey = "TranslationPath";
    private Path isabellePath;
    private Path translationPath;
    private static final Path DEFAULT_ISABELLE_PATH = Path.of(System.getProperty("user.home"), "Isabelle2023");
    private static final Path DEFAULT_TRANSLATION_PATH = Path.of(PathConfig.getKeyConfigDir(), "isabelleTranslations");

    private static Configuration getDefaultConfig() {
        Configuration config = new Configuration();
        config.set(isabellePathKey, DEFAULT_ISABELLE_PATH);
        config.set(translationPathKey, DEFAULT_TRANSLATION_PATH);
        return config;
    }

    private IsabelleTranslationSettings(Configuration load) {
        readSettings(load);
        Runtime.getRuntime().addShutdownHook(new Thread(this::save));
    }

    public Path getIsabellePath() {
        return isabellePath;
    }

    public Path getTranslationPath() {
        return translationPath;
    }


    public static IsabelleTranslationSettings getInstance() {
        if (INSTANCE == null) {
            if (SETTINGS_FILE_NEW.exists()) {
                try {
                    LOGGER.info("Use new configuration format at {}", SETTINGS_FILE_NEW);
                    return INSTANCE = new IsabelleTranslationSettings(Configuration.load(SETTINGS_FILE_NEW));
                } catch (IOException e) {
                    LOGGER.error("Could not read {}", SETTINGS_FILE_NEW, e);
                }
            }
            LOGGER.info("Resorting to default Isabelle settings");
            return INSTANCE = new IsabelleTranslationSettings(getDefaultConfig());
        }
        return INSTANCE;
    }

    public void save() {
            LOGGER.info("Save Isabelle settings to: " + SETTINGS_FILE_NEW.getAbsolutePath());
            try (Writer writer = new FileWriter(SETTINGS_FILE_NEW)) {
                var config = new Configuration();
                writeSettings(config);
                config.save(writer, "Isabelle settings");
                writer.flush();
            } catch (IOException ex) {
                LOGGER.error("Failed to save Isabelle settings", ex);
            }
    }

    @Override
    public void readSettings(Properties props) {
        isabellePath = Path.of(props.getProperty(isabellePathKey));
        translationPath = Path.of(props.getProperty(translationPathKey));
    }

    @Override
    public void writeSettings(Properties props) {
        props.setProperty(isabellePathKey, isabellePath.toString());
        props.setProperty(translationPathKey, translationPath.toString());
    }

    @Override
    public void readSettings(@NonNull Configuration props) {
        isabellePath = Path.of(props.get(isabellePathKey, DEFAULT_ISABELLE_PATH.toString()));
        translationPath = Path.of(props.get(translationPathKey, DEFAULT_TRANSLATION_PATH.toString()));
    }

    @Override
    public void writeSettings(@NonNull Configuration props) {
        props.set(isabellePathKey, isabellePath.toString());
        props.set(translationPathKey, translationPath.toString());
    }
}
