/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.keyshortcuts;

import java.awt.*;
import java.awt.event.InputEvent;
import java.lang.ref.WeakReference;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import javax.swing.*;

/**
 * Manager of the configurable {@link KeyStroke}s for proof macros and GUI actions.
 * <p>
 * If possible, all actions should ask this interface for a {@link KeyStroke}, by calling
 * {@link #lookupAndOverride(Action)}.
 * <p>
 * The general guidelines for adding new keyboard shortcuts are
 * <ul>
 * <li>they must not produce a printable character,
 * <li>they must not interfere with shortcuts already defined by the window manager (this probably
 * includes all combinations using the Windows key),
 * <li>the <a href="http://en.wikipedia.org/wiki/Keyboard_shortcut#.22Sacred.22_keybindings">
 * "sacred keybindings"</a> must not be touched,
 * <li>the theme for strategy macros should be consistent (currently CTRL + SHIFT + letter).
 * </ul>
 *
 * @author bruns
 * @author weigl, 2019-05
 */
public final class KeyStrokeManager {
    /**
     * This constant holds the typical key to be used for shortcuts (usually
     * {@link InputEvent#CTRL_DOWN_MASK})
     */
    public static final int SHORTCUT_KEY_MASK = getShortcutMask();

    /**
     * This constant holds the typical key combination to be used for auxiliary shortcuts
     * ({@link InputEvent#SHIFT_DOWN_MASK} plus usually {@link InputEvent#CTRL_DOWN_MASK})
     */
    public static final int MULTI_KEY_MASK = SHORTCUT_KEY_MASK | InputEvent.SHIFT_DOWN_MASK;

    /**
     * List of actions, that requested a {@link KeyStroke}.
     * <p>
     * Needed for dynamical configurability of the {@link KeyStroke} via {@link ShortcutSettings }
     */
    static final Map<String, WeakReference<Action>> actions = new HashMap<>(100);

    private KeyStrokeManager() {
    }

    /**
     * Get a {@link KeyStroke} for the given <code>key</code>. If no {@link KeyStroke} is defined,
     * <code>defaultValue</code> is returned.
     * <p>
     * Also thsi method sets the determined key stroke in the settings.
     *
     * @param key key
     * @param defaultValue default value
     * @return nullable
     * @see KeyStrokeSettings
     */
    public static KeyStroke get(String key, KeyStroke defaultValue) {
        KeyStroke ks = KeyStrokeSettings.getInstance().getKeyStroke(key, defaultValue);
        KeyStrokeSettings.getInstance().setKeyStroke(key, ks, false);
        return ks;
    }

    /**
     * The same as {@link #get(Object, KeyStroke)} but uses the given object's class name as key.
     *
     * @param action
     * @param defaultValue
     * @return
     */
    public static KeyStroke get(Object action, String defaultValue) {
        return get(action, KeyStroke.getKeyStroke(defaultValue));
    }

    /**
     * The same as {@link #get(Object, KeyStroke)} but uses the given object's class name as key.
     *
     * @param action
     * @param defaultValue
     * @return
     */
    public static KeyStroke get(Object action, KeyStroke defaultValue) {
        return get(action.getClass().getName(), defaultValue);
    }

    /**
     * The same as {@link #get(Object, KeyStroke)} but uses the given object's class name as key and
     * non-default keystroke.
     *
     * @param action
     * @return
     */
    public static KeyStroke get(Object action) {
        return get(action, (KeyStroke) null);
    }

    /**
     * @param action
     * @return
     * @see #lookupAndOverride(Action, String)
     */
    public static KeyStroke lookupAndOverride(Action action) {
        return lookupAndOverride(action, action.getClass().getName());
    }

    /**
     * Lookup a user-defined key stroke via {@link #get(String, KeyStroke)} for the given key. If no
     * key stroke is defined it uses the defined key stroke in the given <code>action</code>.
     * <p>
     * Also adds the action to the list of {@link #actions}.
     *
     * @param action
     * @param key
     * @return
     */
    public static KeyStroke lookupAndOverride(Action action, String key) {
        KeyStroke def = (KeyStroke) action.getValue(Action.ACCELERATOR_KEY);
        KeyStroke found = get(key, def);
        action.putValue(Action.ACCELERATOR_KEY, found);
        registerAction(action);
        return found;
    }

    /**
     * Register an action. Helps later to update the keyboard shortcut.
     */
    public static void registerAction(Action action) {
        actions.put(action.getClass().getName(), new WeakReference<>(action));
    }

    public static KeyStrokeSettings getSettings() {
        return KeyStrokeSettings.getInstance();
    }

    static Action findAction(String clazz) {
        return actions.getOrDefault(clazz, new WeakReference<>(null)).get();
    }

    /**
     * Workaround for running in non-ui mode, e.g., docker images.
     */
    private static int getShortcutMask() {
        try {
            return Toolkit.getDefaultToolkit().getMenuShortcutKeyMaskEx();
        } catch (HeadlessException e) {
            return 0;
        }
    }

    /**
     * Get all the managed actions.
     *
     * @return all actions
     */
    public static Collection<WeakReference<Action>> getAllActions() {
        return actions.values();
    }
}
