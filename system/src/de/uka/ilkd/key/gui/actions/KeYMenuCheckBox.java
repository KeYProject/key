package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.gui.MainWindow;
import java.awt.event.ActionEvent;
import javax.swing.JCheckBoxMenuItem;

/**
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public abstract class KeYMenuCheckBox extends JCheckBoxMenuItem {

    final MainWindowAction mainWindowAction;

    KeYMenuCheckBox(MainWindow mainWindow, String label) {
        super();
        mainWindowAction = new MainWindowAction(mainWindow) {
            @Override
            public void actionPerformed(ActionEvent ae) {
                checkBoxToggled();
            }
        };
        mainWindowAction.setName(label);
        setAction(mainWindowAction);
    }

    public void setTooltip(String s) {
        mainWindowAction.setTooltip(s);
    }

    // Make sure getState() does the same as isVisible().
    @Override
    public boolean getState() {
        return isSelected();
    }

    // Make sure setState() does the same as setVisible().
    @Override
    public void setState(boolean b) {
        setSelected(b);
    }

    public abstract void checkBoxToggled();
}
