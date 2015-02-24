// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.actions;

import java.awt.Desktop;
import java.awt.event.ActionEvent;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.URL;


import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;

/**
 * Open the KeY project homepage in the system default browser.
 * May be inactive if Java 6 Desktop system is not supported or
 * internet connection missing.
 * @author bruns
 *
 */
public class KeYProjectHomepageAction extends MainWindowAction {

    private static final long serialVersionUID = 8657661861116034536L;
    private final static Desktop desktop = Desktop.isDesktopSupported() ? Desktop.getDesktop() : null;
    private final static String url = "http://www.key-project.org/";

    public KeYProjectHomepageAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Online help");
        setEnabled(desktopEnabled());
        setTooltip("Opens the KeY project homepage in the default browser");
        setIcon(IconFactory.help(16));
    }
    
    private static boolean desktopEnabled() {
        return desktop != null && desktop.isSupported(Desktop.Action.BROWSE);
    }
    
    @SuppressWarnings("finally")
    private static URI getURI() {
        URI res = null;
        try {
            res = (new URL(url)).toURI();
        } catch (MalformedURLException e) {
            // todo Auto-generated catch block
        } catch (URISyntaxException e) {
            // todo Auto-generated catch block
        } finally {
            return res;
        }
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        try {
            desktop.browse(getURI());
        } catch (IOException e1) {
            // todo Auto-generated catch block
        }
    }


}