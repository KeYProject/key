package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.gui.extension.api.KeYExtConstants;

import javax.swing.*;
import java.awt.*;

/**
 * @author Alexander Weigl
 * @version 1 (13.02.19)
 */
public abstract class KeyAction extends AbstractAction {
    /**
     * This constant holds the typical key to be used for shortcuts (usually
     * {@link java.awt.Event#CTRL_MASK})
     */
    protected static final int SHORTCUT_KEY_MASK
            = Toolkit.getDefaultToolkit().getMenuShortcutKeyMask();

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

    protected void setAcceleratorKey(KeyStroke keyStroke) {
        putValue(ACCELERATOR_KEY, keyStroke);
    }

    public KeyStroke getAcceleratorKey() {
        return (KeyStroke) getValue(ACCELERATOR_KEY);
    }

    protected String getTooltip() {
        return (String) getValue(Action.SHORT_DESCRIPTION);
    }

    protected void setTooltip(String toolTip) {
        putValue(Action.SHORT_DESCRIPTION, toolTip);
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
        return (String) getValue(KeYExtConstants.PATH);
    }

    protected void setMenuPath(String path) {
        putValue(KeYExtConstants.PATH, path);
    }

    public int getPriority() {
        Integer i = (Integer) getValue(KeYExtConstants.PRIORITY);
        return i == null ? 0 : i;
    }

    protected void setPriority(int priority) {
        putValue(KeYExtConstants.PRIORITY, priority);
    }

}
