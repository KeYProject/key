/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.keyshortcuts;

import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.io.IOException;
import java.io.Writer;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;
import java.util.Properties;
import java.util.TreeMap;
import javax.swing.*;

import de.uka.ilkd.key.gui.actions.*;
import de.uka.ilkd.key.gui.settings.SettingsManager;
import de.uka.ilkd.key.macros.*;
import de.uka.ilkd.key.settings.AbstractPropertiesSettings;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.settings.PathConfig;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager.MULTI_KEY_MASK;
import static de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager.SHORTCUT_KEY_MASK;

/**
 * Class for storing and retrieving {@link KeyStroke}s.
 *
 * If possible, define the keyboard shortcuts in the static block here. By that, it is easier to
 * detect and prevent possible duplicates. In addition, be careful to avoid combinations that are
 * used by the docking framework, such as Ctrl+E or Ctrl+M.
 *
 * @author Alexander Weigl, Wolfram Pfeifer (overhaul, v2)
 * @version 1 (09.05.19)
 * @version 2 (04.08.23)
 */
public class KeyStrokeSettings extends AbstractPropertiesSettings {
    /**
     * filename of the properties file
     */
    public static final String SETTINGS_FILENAME = "keystrokes.properties";

    /**
     * path of the properties file
     */
    public static final Path SETTINGS_FILE =
        PathConfig.getKeyConfigDir().resolve(SETTINGS_FILENAME);
    private static final Path SETTINGS_FILE_NEW =
        PathConfig.getKeyConfigDir().resolve("keystrokes.json");

    private static final Logger LOGGER = LoggerFactory.getLogger(KeyStrokeSettings.class);


    /**
     * singleton instance
     */
    private static KeyStrokeSettings INSTANCE = null;

    /**
     * default {@link KeyStroke}s
     */
    private static Map<String, String> DEFAULT_KEYSTROKES = new TreeMap<>();

    // define the default mappings
    static {
        // use CTRL+SHIFT+letter for macros
        defineDefault(FullAutoPilotProofMacro.class, KeyEvent.VK_V, MULTI_KEY_MASK);
        defineDefault(AutoPilotPrepareProofMacro.class, KeyEvent.VK_D, MULTI_KEY_MASK);
        defineDefault(PropositionalExpansionMacro.class, KeyEvent.VK_A, MULTI_KEY_MASK);
        defineDefault(FullPropositionalExpansionMacro.class, KeyEvent.VK_S, MULTI_KEY_MASK);
        defineDefault(TryCloseMacro.class, KeyEvent.VK_C, MULTI_KEY_MASK);
        defineDefault(FinishSymbolicExecutionMacro.class, KeyEvent.VK_X, MULTI_KEY_MASK);
        defineDefault(OneStepProofMacro.class, KeyEvent.VK_SPACE, MULTI_KEY_MASK);
        defineDefault(HeapSimplificationMacro.class, KeyEvent.VK_H, MULTI_KEY_MASK);
        defineDefault(UpdateSimplificationMacro.class, KeyEvent.VK_L, MULTI_KEY_MASK);
        defineDefault(IntegerSimplificationMacro.class, KeyEvent.VK_I, MULTI_KEY_MASK);
        defineDefault(SMTPreparationMacro.class, KeyEvent.VK_Y, MULTI_KEY_MASK);

        // other actions with Shift + Ctrl + _
        defineDefault(SearchInProofTreeAction.class, KeyEvent.VK_F, MULTI_KEY_MASK);
        defineDefault(PrettyPrintToggleAction.class, KeyEvent.VK_P, MULTI_KEY_MASK);
        defineDefault(UnicodeToggleAction.class, KeyEvent.VK_U, MULTI_KEY_MASK);
        defineDefault(ProofManagementAction.class, KeyEvent.VK_M, MULTI_KEY_MASK);

        // actions with F keys
        defineDefault(QuickSaveAction.class, KeyEvent.VK_F5, 0);
        defineDefault(QuickLoadAction.class, KeyEvent.VK_F6, 0);

        // actions with Ctrl + _
        defineDefault(IncreaseFontSizeAction.class, KeyEvent.VK_PLUS, SHORTCUT_KEY_MASK);
        defineDefault(DecreaseFontSizeAction.class, KeyEvent.VK_MINUS, SHORTCUT_KEY_MASK);
        defineDefault(AbandonTaskAction.class, KeyEvent.VK_W, SHORTCUT_KEY_MASK);
        defineDefault(PruneProofAction.class, KeyEvent.VK_DELETE, SHORTCUT_KEY_MASK);
        defineDefault(GoalBackAction.class, KeyEvent.VK_Z, SHORTCUT_KEY_MASK);
        // does not work at the moment, maybe because the button is not in a menu?
        // defineDefault(UndoHistoryButton.UndoAction.class, KeyEvent.VK_U, SHORTCUT_KEY_MASK);
        defineDefault(CopyToClipboardAction.class, KeyEvent.VK_C, SHORTCUT_KEY_MASK);
        defineDefault(ExitMainAction.class, KeyEvent.VK_Q, SHORTCUT_KEY_MASK);
        defineDefault(GoalSelectAboveAction.class, KeyEvent.VK_K, SHORTCUT_KEY_MASK);
        defineDefault(GoalSelectBelowAction.class, KeyEvent.VK_J, SHORTCUT_KEY_MASK);
        defineDefault(AutoModeAction.class, KeyEvent.VK_SPACE, SHORTCUT_KEY_MASK);
        defineDefault(OpenMostRecentFileAction.class, KeyEvent.VK_R, SHORTCUT_KEY_MASK);
        defineDefault(SaveBundleAction.class, KeyEvent.VK_B, SHORTCUT_KEY_MASK);
        defineDefault(SaveFileAction.class, KeyEvent.VK_S, SHORTCUT_KEY_MASK);
        defineDefault(SettingsManager.ShowSettingsAction.class, KeyEvent.VK_N, SHORTCUT_KEY_MASK);
        // remove as the old menu should not be accessible anymore
        // defineDefault(TacletOptionsAction.class, KeyEvent.VK_T, SHORTCUT_KEY_MASK);
        defineDefault(OpenFileAction.class, KeyEvent.VK_O, SHORTCUT_KEY_MASK);
        defineDefault(SearchInSequentAction.class, KeyEvent.VK_F, SHORTCUT_KEY_MASK);

        // "special" keystrokes
        defineDefault(SearchNextAction.class, KeyEvent.VK_F3, 0);
        defineDefault(SearchPreviousAction.class, KeyEvent.VK_F3, InputEvent.SHIFT_DOWN_MASK);
        defineDefault(SelectionBackAction.class, KeyEvent.VK_LEFT,
            SHORTCUT_KEY_MASK | InputEvent.ALT_DOWN_MASK);
        defineDefault(SelectionForwardAction.class, KeyEvent.VK_RIGHT,
            SHORTCUT_KEY_MASK | InputEvent.ALT_DOWN_MASK);

        /*
         * Do not use this! It produces strange behavior, as the constructor there calls
         * lookupAcceleratorKey() again, which then accesses the partially initialized
         * KeyStrokeSettings. In addition, the rest of the default definitions are not stored then.
         */
        // defineDefault(HelpFacade.ACTION_OPEN_HELP.getClass(), KeyEvent.VK_F1, 0);
    }

    private KeyStrokeSettings(Properties init) {
        super(""); // no category, separate file
        this.properties.putAll(DEFAULT_KEYSTROKES);
        init.forEach((key, value) -> {
            if (value != null && !value.toString().isEmpty()) {
                this.properties.put(key.toString(), value);
            }
        });
        save();
        Runtime.getRuntime().addShutdownHook(new Thread(this::save));
    }

    public KeyStrokeSettings(Configuration config) {
        super("");
        this.properties.putAll(DEFAULT_KEYSTROKES);
        readSettings(config);
        save();
        Runtime.getRuntime().addShutdownHook(new Thread(this::save));
    }

    public static <T> void defineDefault(T any, KeyStroke ks) {
        defineDefault(any.getClass(), ks);
    }

    public static <T> void defineDefault(Class<T> clazz, KeyStroke ks) {
        DEFAULT_KEYSTROKES.put(clazz.getName(), ks.toString());
    }

    // convenience method to make the definitions above better readable
    private static <T> void defineDefault(Class<T> clazz, int keyCode, int modifiers) {
        defineDefault(clazz, KeyStroke.getKeyStroke(keyCode, modifiers));
    }

    private static KeyStrokeSettings loadFromConfig() {
        return new KeyStrokeSettings(SettingsManager.loadProperties(SETTINGS_FILE.toFile()));
    }

    public static KeyStrokeSettings getInstance() {

        if (INSTANCE == null) {
            if (Files.exists(SETTINGS_FILE)) {
                try {
                    LOGGER.info("Use new configuration format at {}", SETTINGS_FILE_NEW);
                    return INSTANCE = new KeyStrokeSettings(Configuration.load(SETTINGS_FILE_NEW));
                } catch (IOException e) {
                    LOGGER.error("Could not read {}", SETTINGS_FILE_NEW, e);
                }
            }
            return INSTANCE = loadFromConfig();
        }
        return INSTANCE;
    }

    @Override
    public void readSettings(Properties props) {
        props.forEach((k, v) -> this.properties.put(k.toString(), v));
    }

    void setKeyStroke(String key, KeyStroke stroke, boolean override) {
        var old = getKeyStroke(key, null);
        if (override || (old == null)) {
            properties.put(key, stroke != null ? stroke.toString() : "");
            firePropertyChange(key, old, stroke);
        }
    }

    KeyStroke getKeyStroke(String key, KeyStroke defaultValue) {
        try {
            KeyStroke ks = KeyStroke.getKeyStroke(properties.get(key).toString());
            if (ks != null) {
                return ks;
            }
        } catch (Exception ignored) {
        }
        return defaultValue;
    }

    public void save() {
        LOGGER.info("Save keyboard shortcuts to: {}", SETTINGS_FILE.toAbsolutePath());
        try {
            Files.createDirectories(SETTINGS_FILE.getParent());
            try (Writer writer = Files.newBufferedWriter(SETTINGS_FILE, StandardCharsets.UTF_8)) {
                Properties props = new Properties();
                for (Map.Entry<String, Object> entry : properties.entrySet()) {
                    props.setProperty(entry.getKey(), entry.getValue().toString());
                }
                props.store(writer, "KeY's KeyStrokes");
            }
        } catch (IOException ex) {
            ex.printStackTrace();
        }

        LOGGER.info("Save keyboard shortcuts to: {}", SETTINGS_FILE_NEW.toAbsolutePath());
        try (Writer writer = Files.newBufferedWriter(SETTINGS_FILE_NEW)) {
            var config = new Configuration(properties);
            config.save(writer, "KeY's KeyStrokes");
            writer.flush();
        } catch (IOException ex) {
            LOGGER.warn("Failed to save", ex);
        }
    }
}
