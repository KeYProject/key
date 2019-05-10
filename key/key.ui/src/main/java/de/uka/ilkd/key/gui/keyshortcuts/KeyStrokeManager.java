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

package de.uka.ilkd.key.gui.keyshortcuts;

import javax.swing.*;
import java.awt.*;
import java.awt.event.KeyEvent;
import java.lang.ref.Reference;
import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.List;

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
    static List<WeakReference<Action>> actions = new ArrayList<>(100);

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
        actions.add(new WeakReference<>(action));
        return found;
    }

    public static KeyStrokeSettings getSettings() {
        return KeyStrokeSettings.getInstance();
    }

    static Action findAction(String clazz) {
        return actions.stream()
                .map(Reference::get)
                .filter(it -> it.getClass().getName().equals(clazz))
                .findAny().orElse(null);
    }
}

