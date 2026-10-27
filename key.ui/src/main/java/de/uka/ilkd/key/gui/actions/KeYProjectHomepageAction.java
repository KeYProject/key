/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.io.IOException;
import java.net.URI;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;

import org.key_project.util.java.SwingUtil;

/**
 * Open the KeY project homepage in the system default browser. May be inactive if Java 6 Desktop
 * system is not supported or internet connection missing.
 *
 * @author bruns
 *
 */
public class KeYProjectHomepageAction extends MainWindowAction {
    private static final long serialVersionUID = 8657661861116034536L;
    private final static String url = "https://www.key-project.org/";

    public KeYProjectHomepageAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("KeY Homepage");
        setEnabled(desktopEnabled());
        setTooltip("Opens the KeY project homepage in the default browser");
        setIcon(IconFactory.help(16));
        lookupAcceleratorKey();
    }

    private static boolean desktopEnabled() {
        return SwingUtil.browseIsSupported();
    }

    private static URI getURI() {
        try {
            return URI.create(url);
        } catch (IllegalArgumentException e) {
            // malformed homepage URL, keep the previous failure semantics
            return null;
        }
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        try {
            SwingUtil.browse(getURI());
        } catch (IOException ignored) {
        }
    }
}
