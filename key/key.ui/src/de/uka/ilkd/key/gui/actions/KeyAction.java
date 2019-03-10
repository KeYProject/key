package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.gui.ext.KeYExtConst;

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

    protected String getName() {
        return (String) getValue(NAME);
    }

    protected void setName(String name) {
        putValue(NAME, name);
    }

    @Deprecated // add a line in gui.utils.KeyStrokeManager instead
    protected void setAcceleratorLetter(int letter) {
        setAcceleratorKey(KeyStroke.getKeyStroke(letter, SHORTCUT_KEY_MASK));
    }

    @Deprecated // add a line in gui.utils.KeyStrokeManager instead
    protected void setAcceleratorKey(KeyStroke keyStroke) {
        putValue(ACCELERATOR_KEY, keyStroke);
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

    protected Icon getIcon(Icon icon) {
        return getSmallIcon();
    }

    protected Icon getSmallIcon() {
        return (Icon) getValue(SMALL_ICON);
    }

    protected void setSmallIcon(Icon icon) {
        putValue(SMALL_ICON, icon);
    }

    protected Icon setLargeIcon() {
        return (Icon) getValue(LARGE_ICON_KEY);
    }

    protected boolean isSelected() {
        return getValue(SELECTED_KEY) == Boolean.TRUE;
    }

    protected void setSelected(Boolean b) {
        putValue(SELECTED_KEY, b);
    }

    protected String getMenuPath() {
        return (String) getValue(KeYExtConst.PATH);
    }

    protected void setMenuPath(String path) {
        putValue(KeYExtConst.PATH, path);
    }

    protected int getPriority() {
        Integer i = (Integer) getValue(KeYExtConst.PRIORITY);
        return i == null ? 0 : i;
    }

    protected void setPriority(int priority) {
        putValue(KeYExtConst.PRIORITY, priority);
    }

}
