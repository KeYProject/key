package de.uka.ilkd.key.gui.actions;

import java.awt.Toolkit;

import javax.swing.AbstractAction;
import javax.swing.Action;
import javax.swing.Icon;
import javax.swing.KeyStroke;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;

public abstract class MainWindowAction extends AbstractAction {

    /**
     * 
     */
    private static final long serialVersionUID = -957832573562266547L;

    /**
     * This constant holds the typical key to be used for shortcuts
     * (usually {@link java.awt.Event#CTRL_MASK})
     */
    protected static final int SHORTCUT_KEY_MASK = 
	Toolkit.getDefaultToolkit().getMenuShortcutKeyMask();
    
    protected final MainWindow mainWindow;

    protected MainWindowAction(MainWindow mainWindow) {
	assert mainWindow != null;
	this.mainWindow = mainWindow;
    }
    
    protected KeYMediator getMediator() {
	return mainWindow.getMediator();
    }

    protected void setName(String name) {
        putValue(NAME, name);
    }

    protected void setAcceleratorLetter(int letter) {
        setAcceleratorKey(KeyStroke.getKeyStroke(letter, SHORTCUT_KEY_MASK));
    }

    protected void setAcceleratorKey(KeyStroke keyStroke) {
        putValue(ACCELERATOR_KEY, keyStroke);
    }

    protected void setTooltip(String toolTip) {
        putValue(Action.SHORT_DESCRIPTION, toolTip);	
    }

    protected void setIcon(Icon icon) {
        putValue(SMALL_ICON, icon);
    }

    protected void setSelected(Boolean b) {
        putValue(SELECTED_KEY, b);
    }

}
