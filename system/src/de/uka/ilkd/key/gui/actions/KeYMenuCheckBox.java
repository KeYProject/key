package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.gui.MainWindow;
import java.awt.event.ActionEvent;
import javax.swing.JCheckBoxMenuItem;

/**
 * This class can be used for adding Checkboxes to the menu.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public abstract class KeYMenuCheckBox extends JCheckBoxMenuItem {

    protected final MainWindowAction mainWindowAction;

    KeYMenuCheckBox(MainWindow mainWindow, String label) {
        final KeYMenuCheckBox checkBox = this;
        mainWindowAction = new MainWindowAction(mainWindow) {
            @Override
            public void actionPerformed(ActionEvent ae) {
                handleClickEvent();
                mainWindow.savePreferences(checkBox);
            }
        };
        mainWindowAction.setName(label);
        setAction(mainWindowAction);
    }

    public void setTooltip(String s) {
        mainWindowAction.setTooltip(s);
    }

    /* 
     * Make sure getState() does the same as isSelected().
     */
    @Override
    public boolean getState() {
        return isSelected();
    }

    /*
     * Make sure setState(boolean) does the same as setSelected(boolean).
     */
    @Override
    public void setState(boolean b) {
        setSelected(b);
    }

    public abstract void handleClickEvent();
}
