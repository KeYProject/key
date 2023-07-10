package de.uka.ilkd.key.gui.docking;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.io.File;
import java.io.IOException;
import java.util.*;
import java.util.List;
import javax.annotation.Nonnull;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.GUIListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeRegular;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager;
import de.uka.ilkd.key.settings.PathConfig;

import bibliothek.gui.dock.common.CControl;
import bibliothek.gui.dock.util.IconManager;
import bibliothek.gui.dock.util.Priority;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Extension for working with layouts.
 *
 * @author Alexander Weigl
 * @version 1 (15.05.19)
 */
@KeYGuiExtension.Info(name = "Docking Helpers", optional = false, experimental = false,
    priority = 1)
public final class DockingLayout implements KeYGuiExtension, KeYGuiExtension.Startup,
        KeYGuiExtension.MainMenu {
    private static final Logger LOGGER = LoggerFactory.getLogger(DockingLayout.class);

    public static final float SIZE_ICON_DOCK = 12f;
    public static final File LAYOUT_FILE = new File(PathConfig.getKeyConfigDir(), "layout.xml");
    public static final String[] LAYOUT_NAMES = new String[] { "Default", "Slot 1", "Slot 2" };
    public static final int[] LAYOUT_KEYS = new int[] { KeyEvent.VK_F11, KeyEvent.VK_F12 };

    private final ButtonGroup layouts = new ButtonGroup();
    private MainWindow window;

    private void installIcons(MainWindow mw) {
        CControl globalPort = mw.getDockControl();
        IconManager icons = globalPort.getController().getIcons();
        Priority p = Priority.CLIENT;

        icons.setIcon("locationmanager.normalize", p,
            IconFontSwing.buildIcon(FontAwesomeRegular.WINDOW_RESTORE, SIZE_ICON_DOCK));

        icons.setIcon("locationmanager.maximize", p,
            IconFontSwing.buildIcon(FontAwesomeRegular.WINDOW_MAXIMIZE, SIZE_ICON_DOCK));

        icons.setIcon("locationmanager.minimize", p,
            IconFontSwing.buildIcon(FontAwesomeRegular.WINDOW_MINIMIZE, SIZE_ICON_DOCK));

        icons.setIcon("locationmanager.externalize", p,
            IconFontSwing.buildIcon(FontAwesomeSolid.EXTERNAL_LINK_SQUARE_ALT, SIZE_ICON_DOCK));

        icons.setIcon("locationmanager.unexternalize", p,
            new ImageIcon(IconFontSwing.buildImage(FontAwesomeSolid.EXTERNAL_LINK_ALT,
                SIZE_ICON_DOCK, Color.black, Math.PI)));

        icons.setIcon("locationmanager.unmaximize_externalized", p,
            IconFontSwing.buildIcon(FontAwesomeSolid.EXTERNAL_LINK_ALT, SIZE_ICON_DOCK));

        icons.setIcon("screen.maximize", p,
            IconFontSwing.buildIcon(FontAwesomeRegular.EDIT, SIZE_ICON_DOCK));

        icons.setIcon("close", p,
            IconFontSwing.buildIcon(FontAwesomeRegular.WINDOW_CLOSE, SIZE_ICON_DOCK));
    }

    private static void loadLayouts(CControl globalPort) {
        try {
            if (LAYOUT_FILE.exists()) {
                globalPort.readXML(LAYOUT_FILE);
            }
        } catch (IOException e) {
            LOGGER.warn("Failed to load layouts", e);
        }
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        this.window = window;
        installIcons(window);
        loadLayouts(window.getDockControl());
        setLayout(LAYOUT_NAMES[0]);
        window.getMediator().addGUIListener(new GUIListener() {
            @Override
            public void modalDialogOpened(EventObject e) {

            }

            @Override
            public void modalDialogClosed(EventObject e) {

            }

            @Override
            public void shutDown(EventObject e) {
                try {
                    window.getDockControl().writeXML(LAYOUT_FILE);
                } catch (IOException ex) {
                    LOGGER.warn("Failed to save layouts ", ex);
                }
            }
        });
    }

    private void setLayout(String layout) {
        CControl globalPort = window.getDockControl();
        boolean defaultLayoutDefined = Arrays.asList(globalPort.layouts()).contains(layout);
        if (defaultLayoutDefined) {
            globalPort.load(layout);
            DockingHelper.restoreMissingPanels(window);
        }
    }

    @Nonnull
    @Override
    public List<JMenuItem> getMainMenuItems(@Nonnull MainWindow mainWindow) {
        List<JMenuItem> items = new ArrayList<>();

        final class ActivateLayoutAction extends MainWindowAction {
            private final String layout;

            private ActivateLayoutAction(MainWindow mainWindow, String layout) {
                super(mainWindow);
                this.layout = layout;
                setName(layout);
                setMenuPath("View.Layout");
            }

            @Override
            public void actionPerformed(ActionEvent e) {
                setLayout(layout);
                layouts.getElements().asIterator().forEachRemaining(
                    button -> button.getModel().setSelected(button.getText().contains(layout)));
            }
        }

        for (String s : LAYOUT_NAMES) {
            JRadioButtonMenuItem button = new JRadioButtonMenuItem(s);
            if (s.equals("Default")) {
                button.getModel().setSelected(true);
            } else {
                button.getModel().setSelected(false);
            }
            layouts.add(button);
            button.setAction(new ActivateLayoutAction(mainWindow, s));
            items.add(button);
        }
        return items;
    }

    @Override
    public List<Action> getMainMenuActions(MainWindow mainWindow) {
        List<Action> actions = new ArrayList<>();

        final class SaveAction extends MainWindowAction {
            private static final long serialVersionUID = -2688272657370615595L;

            private SaveAction(MainWindow mainWindow) {
                super(mainWindow);
                setName("Save Layout");
                setMenuPath("View.Layout");
            }

            @Override
            public void actionPerformed(ActionEvent e) {
                String layout = null;
                var iter = layouts.getElements().asIterator();
                while (iter.hasNext()) {
                    var b = (JRadioButtonMenuItem) iter.next();
                    if (b.getModel().isSelected()) {
                        layout = b.getText();
                        System.out.println("saving in " + layout);
                        break;
                    }
                }
                mainWindow.getDockControl().save(layout);
            }
        }

        final class LoadAction extends MainWindowAction {
            private static final long serialVersionUID = 3130337190207622893L;

            private LoadAction(MainWindow mainWindow) {
                super(mainWindow);
                setName("Load Layout");
                setMenuPath("View.Layout");
            }

            @Override
            public void actionPerformed(ActionEvent e) {
                String layout = null;
                var iter = layouts.getElements().asIterator();
                while (iter.hasNext()) {
                    var b = (JRadioButtonMenuItem) iter.next();
                    if (b.getModel().isSelected()) {
                        layout = b.getText();
                        break;
                    }
                }
                setLayout(layout);
            }
        }

        actions.add(new LoadAction(mainWindow));
        actions.add(new SaveAction(mainWindow));
        actions.add(new ResetLayoutAction(mainWindow));

        return actions;
    }
}


class ResetLayoutAction extends MainWindowAction {
    private static final long serialVersionUID = 8772915552504055750L;

    public ResetLayoutAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Reset Layout");
        KeyStrokeManager.lookupAndOverride(this);
        setMenuPath("View.Layout");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        DockingHelper.restoreFactoryDefault(mainWindow);
        mainWindow.setStatusLine("Factory reset of the layout.");
    }
}
