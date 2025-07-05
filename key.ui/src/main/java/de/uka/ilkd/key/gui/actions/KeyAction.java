/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import javax.swing.AbstractAction;
import javax.swing.Icon;
import javax.swing.KeyStroke;

import de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager;

import java.util.function.Supplier;

import static de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager.SHORTCUT_KEY_MASK;

/// Common class for all "actions" (menu entries / toolbar buttons) the user can trigger.
/// If you want the keyboard shortcuts ([#setAcceleratorKey(KeyStroke)] to work, the action
/// needs to be inserted into the main menu.
///
/// ## Note for implementors
///
/// ### Handling of of the enabledness of an KeY action can be controlled by the predicate variable
/// [#enabledWhen]. This predicate is ask whether the action is enabled in the current state inside
/// the method [#updateEnabledness()]. This machinary requires, that the enabledness of an action
/// is defined as follows in a sub-class:
/// 1. You need to set this variable using [#setEnabledWhen(Supplier<Boolean>)].
/// 2. You also need to add the method [#updateEnabledness()] in the listener,
/// e.g., {@link java.beans.PropertyChangeListener}, s.t. the action is notified on a state change.
///
/// @author Alexander Weigl
/// @version 1 (13.02.19)
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
     * Boolean property set to true if this action should be displayed with a checkbox.
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


    /// Key of the property, [#enabledWhen]
    public static final String PROPERTY_ENABLED_WHEN = "enabledWhen";

    private Pred enabledWhen = () -> true;

    /// Sets the predicate to control the enabledness of this action.
    /// This predicate is requested when [#updateEnabledness()] is called, which is also
    /// by this method, when [#enabledWhen] is updated to a different value.
    ///
    /// @param enabledWhen a supplier of a boolean regarding the enabledness of this action.
    public void setEnabledWhen(Pred enabledWhen) {
        var oldValue = this.enabledWhen;
        this.enabledWhen = enabledWhen;
        firePropertyChange(PROPERTY_ENABLED_WHEN, oldValue, enabledWhen);
        if (oldValue != enabledWhen) {
            updateEnabledness();
        }
    }

    /// @see [#setEnabledWhen(Pred)]
    public Pred getEnabledWhen() {
        return enabledWhen;
    }

    /**
     * Use this method for updating the enabledness using [{@link #enabledWhen}] predicate.
     */
    protected void updateEnabledness() {
        setEnabled(enabledWhen.test());
    }

    public String getName() {
        return (String) getValue(NAME);
    }

    protected void setName(String name) {
        putValue(NAME, name);
    }

    protected void setAcceleratorLetter(int letter) {
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

    protected void setAcceleratorKey(KeyStroke keyStroke) {
        putValue(ACCELERATOR_KEY, keyStroke);
    }

    protected void lookupAcceleratorKey() {
        KeyStrokeManager.lookupAndOverride(this);
    }

    protected void lookupAcceleratorKey(KeyStroke defaultValue) {
        KeyStrokeManager.lookupAndOverride(this, defaultValue.toString());
    }

    protected String getTooltip() {
        return (String) getValue(SHORT_DESCRIPTION);
    }

    protected void setTooltip(String toolTip) {
        putValue(SHORT_DESCRIPTION, toolTip);
    }

    protected void setIcon(Icon icon) {
        putValue(SMALL_ICON, icon);
    }

    protected void setLargeIcon(Icon icon) {
        putValue(LARGE_ICON_KEY, icon);
    }

    public Icon getIcon(Icon icon) {
        return getSmallIcon();
    }

    public Icon getSmallIcon() {
        return (Icon) getValue(SMALL_ICON);
    }

    protected void setSmallIcon(Icon icon) {
        putValue(SMALL_ICON, icon);
    }

    protected Icon setLargeIcon() {
        return (Icon) getValue(LARGE_ICON_KEY);
    }

    public boolean isSelected() {
        return getValue(SELECTED_KEY) == Boolean.TRUE;
    }

    protected void setSelected(Boolean b) {
        putValue(SELECTED_KEY, b);
    }

    public String getMenuPath() {
        return (String) getValue(PATH);
    }

    protected void setMenuPath(String path) {
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
    protected void setPriority(int priority) {
        putValue(PRIORITY, priority);
    }

    /// A stupid interface which is like [#java.util.function.Predicate] but without an argument.
    /// The JDK alternative [#java.util.function.BooleanSupplier] does not provide combinatorial functions.
    /// @author weigl
    interface Pred {
        boolean test();

        default Pred not() {
            return () -> !test();
        }

        default Pred and(Pred other) {
            return () -> test() && other.test();
        }

        default Pred or(Pred other) {
            return () -> test() || other.test();
        }
    }
}
