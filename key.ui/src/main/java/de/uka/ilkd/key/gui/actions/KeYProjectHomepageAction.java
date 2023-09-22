/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.URL;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;

/**
 * Open the KeY project homepage in the system default browser. May be inactive if Java 6 Desktop
 * system is not supported or internet connection missing.
 *
 * @author bruns
 *
 */
public class KeYProjectHomepageAction extends MainWindowAction {

    private static final long serialVersionUID = 8657661861116034536L;
    private final static String url = "http://www.key-project.org/";

    public KeYProjectHomepageAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("KeY Homepage");
        setEnabled(desktopEnabled());
        setTooltip("Opens the KeY project homepage in the default browser");
        setIcon(IconFactory.help(16));
        lookupAcceleratorKey();
    }

    private static boolean desktopEnabled() {
        return Desktop.getDesktop().isSupported(Desktop.Action.BROWSE);
    }

    private static URI getURI() {
        URI res = null;
        try {
            res = (new URL(url)).toURI();
        } catch (MalformedURLException | URISyntaxException e) {
            // todo Auto-generated catch block
        }
        return res;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        try {
            Desktop.getDesktop().browse(getURI());
        } catch (IOException e1) {
            // todo Auto-generated catch block
        }
    }
}
