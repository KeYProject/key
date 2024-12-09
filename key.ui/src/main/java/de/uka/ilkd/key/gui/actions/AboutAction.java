/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.util.KeYConstants;
import de.uka.ilkd.key.util.UnicodeHelper;

public class AboutAction extends MainWindowAction {

    /**
     *
     */
    private static final long serialVersionUID = 8240213594748334802L;

    public AboutAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("About KeY");
        setIcon(IconFactory.help(16));
        // About KeY
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        showAbout();
    }

    public void showAbout() {

        JOptionPane.showMessageDialog(mainWindow,
            new Object[] { IconFactory.keyVersionLogo(),
                KeYConstants.COPYRIGHT.replace("and", "\n" + UnicodeHelper.emSpaces(8) + "and")
                    + "\n\nWWW: http://key-project.org/" + "\n\nVersion " + KeYConstants.VERSION },
            "The KeY Project", JOptionPane.INFORMATION_MESSAGE);

        // JOptionPane pane = new JOptionPane(
        // KeYConstants.COPYRIGHT.replace("and", "\n"+UnicodeHelper.emSpaces(8)+"and")
        // + "\n\nWWW: http://key-project.org/"
        // + "\n\nVersion " + KeYConstants.VERSION
        // , JOptionPane.INFORMATION_MESSAGE,
        // JOptionPane.DEFAULT_OPTION, IconFactory.keyVersionLogo(108, 68));
        // JDialog dialog = pane.createDialog(mainWindow, "The KeY Project");
        // dialog.setVisible(true);
    }

}
