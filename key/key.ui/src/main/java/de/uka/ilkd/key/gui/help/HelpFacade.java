package de.uka.ilkd.key.gui.help;

import bibliothek.gui.dock.common.action.CAction;
import bibliothek.gui.dock.common.action.CButton;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.fonticons.IconFactory;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import java.io.IOException;
import java.net.URI;
import java.net.URISyntaxException;

/**
 * A gate to the KeY documentation system.
 * <p>
 * Provides the facility to open the documentation at press of F1.
 * The opened page is determined context-sensitive by the current focused component
 * and parent components. Specify the URL via {@HelpInfo}.
 *
 * @author Alexander Weigl
 * @version 1 (10.04.19)
 */
public class HelpFacade {
    /**
     * System property key for setting the base url of the help system.
     */
    public static final String KEY_HELP_URL = "key.help.url";

    /**
     * @see OpenHelpAction
     */
    public static final KeyAction ACTION_OPEN_HELP = new OpenHelpAction();

    /**
     * The base url of the help system.
     *
     * @see #KEY_HELP_URL
     */
    public static String HELP_BASE_URL = "https://key-project.org/docs/";

    static {
        if (System.getProperty("KEY_HELP_URL") != null) {
            HELP_BASE_URL = System.getProperty(KEY_HELP_URL);
        }
    }

    private static void openHelpInBrowser(String url) {
        try {
            Desktop.getDesktop().browse(new URI(url));
        } catch (IOException | URISyntaxException e) {
            e.printStackTrace();
        }
    }

    /**
     * Opens the key documentation website in the default system browser.
     */
    public static void openHelp() {
        openHelpInBrowser(HELP_BASE_URL);
    }

    /**
     * Opens the specified sub page of the key
     * documentation website in the default system browser.
     *
     * @param path a valid suffix to the current URI
     */
    public static void openHelp(String path) {
        openHelpInBrowser(HELP_BASE_URL + path);
    }

    /**
     * Tries to find the documentation of the given component and opens it.
     * <p>
     * The documentation is determined by following the parents to the root and checking
     * for {@see HelpInfo} on the classes.
     *
     * @param path
     */
    public static void openHelp(Component path) {
        while (path != null) {
            if (openHelpOfClass(path.getClass()))
                break;
            else
                path = path.getParent();
        }
    }


    /**
     * Opens documentation given for the given class.
     * <p>
     * The class needs to be annotated with {@see HelpInfo}.
     *
     * @param clazz non-null class instance.
     */
    public static boolean openHelpOfClass(Class<?> clazz) {
        HelpInfo help = clazz.getAnnotation(HelpInfo.class);
        if (help != null) {
            openHelpInBrowser(HELP_BASE_URL + help.path());
            return true;
        }
        return false;
    }

    /**
     * Creates a {@link CButton}, that can be add to dockables and opens the given
     * help pages at {@link #HELP_BASE_URL}
     * @param s path to help page
     * @return
     */
    public static CAction createHelpButton(String s) {
        CButton btn = new CButton("", IconFactory.HELP.get());
        btn.addActionListener(e -> openHelp(s));
        return btn;
    }

    private static class OpenHelpAction extends KeyAction {
        private static final long serialVersionUID = 85722762932429493L;

        public OpenHelpAction() {
            setName("Open help");
            setAcceleratorKey(KeyStroke.getKeyStroke(KeyEvent.VK_F1, 0));
            lookupAcceleratorKey();
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            if (e != null && e.getSource() != null) {
                HelpFacade.openHelp((JComponent) e.getSource());
            }
        }
    }
}
