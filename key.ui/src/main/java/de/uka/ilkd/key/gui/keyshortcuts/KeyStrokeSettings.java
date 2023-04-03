package de.uka.ilkd.key.gui.keyshortcuts;

import java.awt.event.KeyEvent;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.nio.charset.StandardCharsets;
import java.util.Properties;
import javax.swing.*;

import de.uka.ilkd.key.gui.actions.*;
import de.uka.ilkd.key.gui.help.HelpFacade;
import de.uka.ilkd.key.gui.settings.SettingsManager;
import de.uka.ilkd.key.macros.*;
import de.uka.ilkd.key.settings.AbstractPropertiesSettings;
import de.uka.ilkd.key.settings.PathConfig;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * A settings for storing and retrieving {@link KeyStroke}s.
 *
 * @author Alexander Weigl
 * @version 1 (09.05.19)
 */
public class KeyStrokeSettings extends AbstractPropertiesSettings {
    /**
     * filename of the properties file
     */
    public static final String SETTINGS_FILENAME = "keystrokes.properties";

    /**
     * path of the properties file
     */
    public static final File SETTINGS_FILE =
        new File(PathConfig.getKeyConfigDir(), KeyStrokeSettings.SETTINGS_FILENAME);

    private static final Logger LOGGER = LoggerFactory.getLogger(KeyStrokeSettings.class);

    /**
     * singleton instance
     */
    private static KeyStrokeSettings INSTANCE = null;

    /**
     * default {@link KeyStroke}s
     */
    private static final Properties DEFAULT_KEYSTROKES = new Properties();

    static {
        if (KeyStrokeManager.FKEY_MACRO_SCHEME) {
            // use F keys for macros, CTRL+SHIFT+letter for other actions
            defineDefault(FullAutoPilotProofMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_F1, 0));
            defineDefault(AutoPilotPrepareProofMacro.class,
                KeyStroke.getKeyStroke(KeyEvent.VK_F2, 0));
            defineDefault(PropositionalExpansionMacro.class,
                KeyStroke.getKeyStroke(KeyEvent.VK_F3, 0));
            defineDefault(FullPropositionalExpansionMacro.class,
                KeyStroke.getKeyStroke(KeyEvent.VK_F4, 0));
            defineDefault(TryCloseMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_F5, 0));
            defineDefault(FinishSymbolicExecutionMacro.class,
                KeyStroke.getKeyStroke(KeyEvent.VK_F6, 0));
            defineDefault(OneStepProofMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_F7, 0));
            defineDefault(HeapSimplificationMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_F9, 0));
            defineDefault(UpdateSimplificationMacro.class,
                KeyStroke.getKeyStroke(KeyEvent.VK_F10, 0));
            defineDefault(IntegerSimplificationMacro.class,
                KeyStroke.getKeyStroke(KeyEvent.VK_F11, 0));
            defineDefault(QuickSaveAction.class,
                KeyStroke.getKeyStroke(KeyEvent.VK_S, KeyStrokeManager.MULTI_KEY_MASK));
            defineDefault(QuickLoadAction.class,
                KeyStroke.getKeyStroke(KeyEvent.VK_O, KeyStrokeManager.MULTI_KEY_MASK));
        } else {
            // use CTRL+SHIFT+letter for macros, F keys for other actions
            defineDefault(FullAutoPilotProofMacro.class,
                KeyStroke.getKeyStroke(KeyEvent.VK_V, KeyStrokeManager.MULTI_KEY_MASK));
            defineDefault(AutoPilotPrepareProofMacro.class,
                KeyStroke.getKeyStroke(KeyEvent.VK_D, KeyStrokeManager.MULTI_KEY_MASK));
            defineDefault(PropositionalExpansionMacro.class,
                KeyStroke.getKeyStroke(KeyEvent.VK_A, KeyStrokeManager.MULTI_KEY_MASK));
            defineDefault(FullPropositionalExpansionMacro.class,
                KeyStroke.getKeyStroke(KeyEvent.VK_S, KeyStrokeManager.MULTI_KEY_MASK));
            defineDefault(TryCloseMacro.class,
                KeyStroke.getKeyStroke(KeyEvent.VK_C, KeyStrokeManager.MULTI_KEY_MASK));
            defineDefault(FinishSymbolicExecutionMacro.class,
                KeyStroke.getKeyStroke(KeyEvent.VK_X, KeyStrokeManager.MULTI_KEY_MASK));
            defineDefault(OneStepProofMacro.class,
                KeyStroke.getKeyStroke(KeyEvent.VK_SPACE, KeyStrokeManager.MULTI_KEY_MASK));
            defineDefault(HeapSimplificationMacro.class,
                KeyStroke.getKeyStroke(KeyEvent.VK_H, KeyStrokeManager.MULTI_KEY_MASK));
            defineDefault(UpdateSimplificationMacro.class,
                KeyStroke.getKeyStroke(KeyEvent.VK_L, KeyStrokeManager.MULTI_KEY_MASK));
            defineDefault(IntegerSimplificationMacro.class,
                KeyStroke.getKeyStroke(KeyEvent.VK_I, KeyStrokeManager.MULTI_KEY_MASK));
            defineDefault(SMTPreparationMacro.class,
                KeyStroke.getKeyStroke(KeyEvent.VK_Y, KeyStrokeManager.MULTI_KEY_MASK));
            defineDefault(KeYProjectHomepageAction.class,
                KeyStroke.getKeyStroke(KeyEvent.VK_F1, 0));
            defineDefault(QuickSaveAction.class, KeyStroke.getKeyStroke(KeyEvent.VK_F5, 0));
            defineDefault(QuickLoadAction.class, KeyStroke.getKeyStroke(KeyEvent.VK_F6, 0));
        }

        // default mappings
        defineDefault(HelpFacade.ACTION_OPEN_HELP.getClass(), KeyStroke.getKeyStroke("F1"));
        defineDefault(OpenExampleAction.class,
            KeyStroke.getKeyStroke(KeyEvent.VK_E, KeyStrokeManager.MULTI_KEY_MASK));
        defineDefault(EditMostRecentFileAction.class,
            KeyStroke.getKeyStroke(KeyEvent.VK_E, KeyStrokeManager.MULTI_KEY_MASK));
        defineDefault(PrettyPrintToggleAction.class,
            KeyStroke.getKeyStroke(KeyEvent.VK_P, KeyStrokeManager.MULTI_KEY_MASK));
        defineDefault(UnicodeToggleAction.class,
            KeyStroke.getKeyStroke(KeyEvent.VK_U, KeyStrokeManager.MULTI_KEY_MASK));
        defineDefault(IncreaseFontSizeAction.class,
            KeyStroke.getKeyStroke(KeyEvent.VK_PLUS, KeyStrokeManager.MULTI_KEY_MASK));
        defineDefault(DecreaseFontSizeAction.class,
            KeyStroke.getKeyStroke(KeyEvent.VK_MINUS, KeyStrokeManager.MULTI_KEY_MASK));

        defineDefault(PruneProofAction.class, KeyStroke.getKeyStroke(KeyEvent.VK_DELETE, 0));
        defineDefault(GoalBackAction.class,
            KeyStroke.getKeyStroke(KeyEvent.VK_Z, KeyStrokeManager.SHORTCUT_KEY_MASK));
    }

    private KeyStrokeSettings(Properties init) {
        this.properties.putAll(DEFAULT_KEYSTROKES);
        init.forEach((key, value) -> {
            if (value != null && !value.toString().isEmpty()) {
                this.properties.put(key, value);
            }
        });
        save();
        Runtime.getRuntime().addShutdownHook(new Thread(this::save));
    }

    public static <T> void defineDefault(T any, KeyStroke ks) {
        defineDefault(any.getClass(), ks);
    }

    public static <T> void defineDefault(Class<T> clazz, KeyStroke ks) {
        DEFAULT_KEYSTROKES.setProperty(clazz.getName(), ks.toString());
    }

    static KeyStrokeSettings loadFromConfig() {
        return new KeyStrokeSettings(SettingsManager.loadProperties(SETTINGS_FILE));
    }

    public static KeyStrokeSettings getInstance() {
        if (INSTANCE == null) {
            INSTANCE = KeyStrokeSettings.loadFromConfig();
        }
        return INSTANCE;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void readSettings(Properties props) {
        properties.putAll(props);
    }

    void setKeyStroke(String key, KeyStroke stroke, boolean override) {
        boolean exists = properties.contains(key);
        if (override || !exists) {
            properties.setProperty(key, stroke != null ? stroke.toString() : "");
            fireSettingsChange();
        }
    }

    KeyStroke getKeyStroke(String key, KeyStroke defaultValue) {
        try {
            KeyStroke ks = KeyStroke.getKeyStroke(properties.getProperty(key));
            if (ks != null) {
                return ks;
            }
        } catch (Exception e) {
        }
        return defaultValue;
    }

    public void save() {
        LOGGER.info("Save keyboard shortcuts to: " + SETTINGS_FILE.getAbsolutePath());
        SETTINGS_FILE.getParentFile().mkdirs();
        try (Writer writer = new FileWriter(SETTINGS_FILE, StandardCharsets.UTF_8)) {
            properties.store(writer, "KeY's KeyStrokes");
            writer.flush();
        } catch (IOException ex) {
            LOGGER.warn("Failed to save", ex);
        }
    }
}
