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

package de.uka.ilkd.key.gui.utilities;

import de.uka.ilkd.key.gui.actions.*;
import de.uka.ilkd.key.gui.help.HelpFacade;
import de.uka.ilkd.key.macros.*;
import de.uka.ilkd.key.settings.AbstractPropertiesSettings;
import de.uka.ilkd.key.settings.PathConfig;

import javax.swing.*;
import java.awt.*;
import java.awt.event.KeyEvent;
import java.io.*;
import java.util.Properties;

/**
 * Manages keyboard shortcuts for proof macros and GUI actions.
 * If possible, all keyboard shortcuts should be defined here and
 * accessed through one of the <code>lookupAndOverride()</code> methods.
 * The general guidelines for adding new keyboard shortcuts are<ul>
 * <li> they must not produce a printable character,
 * <li> they must not interfere with shortcuts already defined by the
 * window manager (this probably includes all combinations using the Windows key),
 * <li> the <a href="http://en.wikipedia.org/wiki/Keyboard_shortcut#.22Sacred.22_keybindings">
 * "sacred keybindings"</a> must not be touched,
 * <li> the theme for strategy macros should be consistent
 * (currently either F keys or CTRL + SHIFT + letter).
 * </ul>
 *
 * @author bruns
 */
public final class KeyStrokeManager {
    /**
     * This constant holds the typical key to be used for shortcuts
     * (usually {@link java.awt.Event#CTRL_MASK})
     */
    public static final int SHORTCUT_KEY_MASK = Toolkit.getDefaultToolkit().getMenuShortcutKeyMask();
    /**
     * If true, F keys are used for macros, otherwise CTRL+SHIFT+letter.
     */
    static final boolean FKEY_MACRO_SCHEME = Boolean.getBoolean("key.gui.fkeyscheme");
    /**
     * This constant holds the typical key combination to be used for auxiliary shortcuts
     * ({@link KeyEvent#SHIFT_MASK} plus usually {@link KeyEvent#CTRL_MASK})
     */
    static final int MULTI_KEY_MASK = SHORTCUT_KEY_MASK | KeyEvent.SHIFT_DOWN_MASK;

    public static KeyStroke get(String key, KeyStroke defaultValue) {
        KeyStroke ks = KeyStrokeSettings.getInstance().getKeyStroke(key, defaultValue);
        KeyStrokeSettings.getInstance().setKeyStroke(key, ks, false);
        return ks;
    }

    /**
     * @param action
     * @param defaultValue
     * @return
     */
    public static KeyStroke get(Object action, String defaultValue) {
        return get(action, KeyStroke.getKeyStroke(defaultValue));
    }

    /**
     * @param action
     * @param defaultValue
     * @return
     */
    public static KeyStroke get(Object action, KeyStroke defaultValue) {
        return get(action.getClass().getName(), defaultValue);
    }

    /**
     * @param action
     * @return
     */
    public static KeyStroke get(Object action) {
        return get(action, (KeyStroke) null);
    }

    /**
     * @param action
     * @return
     */
    public static KeyStroke lookupAndOverride(Action action) {
        KeyStroke def = (KeyStroke) action.getValue(Action.ACCELERATOR_KEY);
        KeyStroke found = get(action, def);
        action.putValue(Action.ACCELERATOR_KEY, found);
        return found;
    }
}

class KeyStrokeSettings extends AbstractPropertiesSettings {
    private static final String SETTINGS_FILENAME = "keystrokes.properties";
    private static final File SETTINGS_FILE = new File(PathConfig.getKeyConfigDir(), KeyStrokeSettings.SETTINGS_FILENAME);
    private static KeyStrokeSettings INSTANCE = null;

    private static Properties DEFAULT_KEYSTROKES = new Properties();

    static {
        if (KeyStrokeManager.FKEY_MACRO_SCHEME) {
            // use F keys for macros, CTRL+SHIFT+letter for other actions
            defineDefault(FullAutoPilotProofMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_F1, 0));
            defineDefault(AutoPilotPrepareProofMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_F2, 0));
            defineDefault(PropositionalExpansionMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_F3, 0));
            defineDefault(FullPropositionalExpansionMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_F4, 0));
            defineDefault(TryCloseMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_F5, 0));
            defineDefault(FinishSymbolicExecutionMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_F6, 0));
            defineDefault(OneStepProofMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_F7, 0));
            defineDefault(HeapSimplificationMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_F9, 0));
            defineDefault(TestGenMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_F8, 0));
            defineDefault(UpdateSimplificationMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_F10, 0));
            defineDefault(IntegerSimplificationMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_F11, 0));
            defineDefault(QuickSaveAction.class, KeyStroke.getKeyStroke(KeyEvent.VK_S, KeyStrokeManager.MULTI_KEY_MASK));
            defineDefault(QuickLoadAction.class, KeyStroke.getKeyStroke(KeyEvent.VK_O, KeyStrokeManager.MULTI_KEY_MASK));
        } else {
            // use CTRL+SHIFT+letter for macros, F keys for other actions
            defineDefault(FullAutoPilotProofMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_V, KeyStrokeManager.MULTI_KEY_MASK));
            defineDefault(AutoPilotPrepareProofMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_D, KeyStrokeManager.MULTI_KEY_MASK));
            defineDefault(PropositionalExpansionMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_A, KeyStrokeManager.MULTI_KEY_MASK));
            defineDefault(FullPropositionalExpansionMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_S, KeyStrokeManager.MULTI_KEY_MASK));
            defineDefault(TryCloseMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_C, KeyStrokeManager.MULTI_KEY_MASK));
            defineDefault(FinishSymbolicExecutionMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_X, KeyStrokeManager.MULTI_KEY_MASK));
            defineDefault(OneStepProofMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_SPACE, KeyStrokeManager.MULTI_KEY_MASK));
            defineDefault(TestGenMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_T, KeyStrokeManager.MULTI_KEY_MASK));
            defineDefault(HeapSimplificationMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_H, KeyStrokeManager.MULTI_KEY_MASK));
            defineDefault(UpdateSimplificationMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_L, KeyStrokeManager.MULTI_KEY_MASK));
            defineDefault(IntegerSimplificationMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_I, KeyStrokeManager.MULTI_KEY_MASK));
            defineDefault(SMTPreparationMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_Y, KeyStrokeManager.MULTI_KEY_MASK));
            defineDefault(KeYProjectHomepageAction.class, KeyStroke.getKeyStroke(KeyEvent.VK_F1, 0));
            defineDefault(QuickSaveAction.class, KeyStroke.getKeyStroke(KeyEvent.VK_F5, 0));
            defineDefault(QuickLoadAction.class, KeyStroke.getKeyStroke(KeyEvent.VK_F6, 0));
        }

        // default mappings
        defineDefault(HelpFacade.ACTION_OPEN_HELP.getClass(), KeyStroke.getKeyStroke("F1"));
        defineDefault(OpenExampleAction.class, KeyStroke.getKeyStroke(KeyEvent.VK_E, KeyStrokeManager.MULTI_KEY_MASK));
        defineDefault(EditMostRecentFileAction.class, KeyStroke.getKeyStroke(KeyEvent.VK_E, KeyStrokeManager.MULTI_KEY_MASK));
        defineDefault(PrettyPrintToggleAction.class, KeyStroke.getKeyStroke(KeyEvent.VK_P, KeyStrokeManager.MULTI_KEY_MASK));
        defineDefault(UnicodeToggleAction.class, KeyStroke.getKeyStroke(KeyEvent.VK_U, KeyStrokeManager.MULTI_KEY_MASK));
        defineDefault(IncreaseFontSizeAction.class, KeyStroke.getKeyStroke(KeyEvent.VK_PLUS, KeyStrokeManager.MULTI_KEY_MASK));
        defineDefault(DecreaseFontSizeAction.class, KeyStroke.getKeyStroke(KeyEvent.VK_MINUS, KeyStrokeManager.MULTI_KEY_MASK));

        defineDefault(PruneProofAction.class,
                KeyStroke.getKeyStroke(KeyEvent.VK_DELETE, 0));
        defineDefault(GoalBackAction.class,
                KeyStroke.getKeyStroke(KeyEvent.VK_Z, KeyStrokeManager.SHORTCUT_KEY_MASK));
    }

    private KeyStrokeSettings(Properties properties) {
        //combine with default values
        Properties p = new Properties(DEFAULT_KEYSTROKES);
        p.putAll(properties);

        //set internally
        readSettings(p);
        // save now and on close
        save();
        Runtime.getRuntime().addShutdownHook(new Thread(this::save));
    }

    private static <T> void defineDefault(T any, KeyStroke ks) {
        defineDefault(any.getClass(), ks);
    }

    private static <T> void defineDefault(Class<T> clazz, KeyStroke ks) {
        DEFAULT_KEYSTROKES.setProperty(clazz.getName(), ks.toString());
    }

    static KeyStrokeSettings loadFromConfig() {
        Properties props = new Properties();
        if (SETTINGS_FILE.exists()) {
            try (FileReader reader = new FileReader(SETTINGS_FILE)) {
                props.load(reader);
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
        return new KeyStrokeSettings(props);
    }

    public static KeyStrokeSettings getInstance() {
        if (INSTANCE == null) INSTANCE = KeyStrokeSettings.loadFromConfig();
        return INSTANCE;
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
            if (ks != null) return ks;
        } catch (Exception e) {
        }
        return defaultValue;
    }

    public void save() {
        System.out.println("Save keyboard shortcuts to: " + SETTINGS_FILE.getAbsolutePath());
        try (Writer writer = new FileWriter(SETTINGS_FILE)) {
            properties.store(writer, "KeY's KeyStrokes");
            writer.flush();
        } catch (IOException ex) {
            ex.printStackTrace();
        }
    }
}
