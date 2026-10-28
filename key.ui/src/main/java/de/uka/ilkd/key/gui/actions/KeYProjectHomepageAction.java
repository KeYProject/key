/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.URL;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;

import org.key_project.util.java.SwingUtil;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Open the KeY project homepage in the system default browser. May be inactive if Java 6 Desktop
 * system is not supported or internet connection missing.
 *
 * @author bruns
 *
 */
@NullMarked
public class KeYProjectHomepageAction extends MainWindowAction {
    private static final long serialVersionUID = 8657661861116034536L;
    private final static String url = "https://www.key-project.org/";

    /**
     * The action-configuration calls operate on {@code this} while the receiver is still under
     * initialization (EISOP initialization check); safe here, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
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

    private static @Nullable URI getURI() {
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
        URI uri = getURI();
        if (uri == null) {
            // The homepage URI is a compile-time constant; the loop below only fails for
            // impossible URL syntax errors, mirroring the previous NPE-guarded behavior.
            throw new NullPointerException("Cannot construct the KeY project homepage URI.");
        }
        try {
            SwingUtil.browse(uri);
        } catch (IOException ignored) {
        }
    }
}
