/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import javax.swing.*;

import de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager;

import org.checkerframework.checker.initialization.qual.UnderInitialization;

import static de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager.SHORTCUT_KEY_MASK;

/**
 * Common class for all "actions" (menu entries / toolbar buttons) the user can trigger.
 * If you want the keyboard shortcuts ({@link #setAcceleratorKey(KeyStroke)} to work, the action
 * needs to be inserted into the main menu.
 *
 * @author Alexander Weigl
 * @version 1 (13.02.19)
 */
public abstract class KeyAction extends AbstractAction {
    /**
     * SHORTCUT_FOCUSED_CONDITION
     */
    public static final String SHORTCUT_FOCUSED_CONDITION = "SHORTCUT_FOCUSED_CONDITION";

    /**
     * Additional key for {@link javax.swing.Action}s. Describes the priority, and therefor an order
     * to arrange these actions.
     */
    public static final String PRIORITY = "PRIORITY";

    /**
     * Additional key for {@link javax.swing.Action}s. Describes a path in a menu where an action
     * should be injected in.
     * <p>
     * The path should be a dot-separated string, i.e. "Heatmap.Options" would inject an action into
     * a sub-sub Menu Options below Heatmap.
     * <p>
     * (see {@code KeYGuiExtensionFacade.findMenu(JMenu, Iterator)})
     */
    public static final String PATH = "PATH";

    /**
     * Boolean property set to true if the this action should be displayed with a checkbox.
     */
    public static final String CHECKBOX = "CHECKBOX";

    /**
     * Key for defining local shortcuts which are prefered used by
     * {@link de.uka.ilkd.key.gui.extension.api.KeYGuiExtension.KeyboardShortcuts}. In comparision
     * with {@code ACCELERATOR_KEY} which should be used for global shortcuts.
     * <p>
     * The stored values are {@link KeyStroke}.
     */
    public static final String LOCAL_ACCELERATOR = "LOCAL_ACCELERATOR";

    public String getName() {
        return (String) getValue(NAME);
    }

    protected void setName(@UnderInitialization KeyAction this, String name) {
        putValue(NAME, name);
    }

    protected void setAcceleratorLetter(@UnderInitialization KeyAction this, int letter) {
        setAcceleratorKey(KeyStroke.getKeyStroke(letter, SHORTCUT_KEY_MASK));
    }

    public int getMnemonic() {
        return (int) getValue(MNEMONIC_KEY);
    }

    protected void setMnemonic(int c) {
        putValue(MNEMONIC_KEY, c);
    }

    public KeyStroke getAcceleratorKey() {
        return (KeyStroke) getValue(ACCELERATOR_KEY);
    }

    protected void setAcceleratorKey(@UnderInitialization KeyAction this, KeyStroke keyStroke) {
        putValue(ACCELERATOR_KEY, keyStroke);
    }

    protected void lookupAcceleratorKey() {
        KeyStrokeManager.lookupAndOverride(this);
    }

    protected void lookupAcceleratorKey(@UnderInitialization KeyAction this,
            KeyStroke defaultValue) {
        KeyStrokeManager.lookupAndOverride(this, defaultValue.toString());
    }

    protected String getTooltip() {
        return (String) getValue(Action.SHORT_DESCRIPTION);
    }

    protected void setTooltip(@UnderInitialization KeyAction this, String toolTip) {
        putValue(Action.SHORT_DESCRIPTION, toolTip);
    }

    protected void setIcon(Icon icon) {
        putValue(SMALL_ICON, icon);
    }

    protected void setLargeIcon(@UnderInitialization KeyAction this, Icon icon) {
        putValue(LARGE_ICON_KEY, icon);
    }

    public Icon getIcon(Icon icon) {
        return getSmallIcon();
    }

    public Icon getSmallIcon() {
        return (Icon) getValue(SMALL_ICON);
    }

    protected void setSmallIcon(@UnderInitialization KeyAction this, Icon icon) {
        putValue(SMALL_ICON, icon);
    }

    protected Icon setLargeIcon() {
        return (Icon) getValue(LARGE_ICON_KEY);
    }

    public boolean isSelected() {
        return getValue(SELECTED_KEY) == Boolean.TRUE;
    }

    protected void setSelected(@UnderInitialization KeyAction this, Boolean b) {
        putValue(SELECTED_KEY, b);
    }

    public String getMenuPath() {
        return (String) getValue(PATH);
    }

    protected void setMenuPath(@UnderInitialization KeyAction this, String path) {
        putValue(PATH, path);
    }

    public int getPriority() {
        Integer i = (Integer) getValue(PRIORITY);
        return i == null ? 0 : i;
    }

    /**
     * Set the priority of this action. Actions are sorted from low priority to high priority.
     *
     * @param priority integer value
     */
    protected void setPriority(@UnderInitialization KeyAction this, int priority) {
        putValue(PRIORITY, priority);
    }
}
