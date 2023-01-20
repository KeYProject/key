package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.URL;

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
        setName("Online Help");
        setEnabled(desktopEnabled());
        setTooltip("Opens the KeY project homepage in the default browser");
        setIcon(IconFactory.help(16));
    }

    private static boolean desktopEnabled() {
        return Desktop.getDesktop().isSupported(Desktop.Action.BROWSE);
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
            Desktop.getDesktop().browse(getURI());
        } catch (IOException e1) {
            // todo Auto-generated catch block
        }
    }
}
