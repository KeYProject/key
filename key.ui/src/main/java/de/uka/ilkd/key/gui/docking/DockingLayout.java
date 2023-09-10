/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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

    private static final float SIZE_ICON_DOCK = 12f;
    private static final File LAYOUT_FILE = new File(PathConfig.getKeyConfigDir(), "layout.xml");
    private static final String[] LAYOUT_NAMES = new String[] { "Default", "Slot 1", "Slot 2" };
    private static final int[] LAYOUT_KEYS =
        new int[] { KeyEvent.VK_F10, KeyEvent.VK_F11, KeyEvent.VK_F12 };

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
                    LOGGER.warn("Failed to save layouts", ex);
                }
            }
        });
    }

    private void setLayout(String layout) {
        CControl globalPort = window.getDockControl();
        boolean defaultLayoutDefined = Arrays.asList(globalPort.layouts()).contains(layout);
        if (defaultLayoutDefined) {
            globalPort.load(layout);
        }
        DockingHelper.restoreMissingPanels(window);
    }

    @Nonnull
    @Override
    public List<Action> getMainMenuActions(@Nonnull MainWindow mainWindow) {
        List<Action> actions = new ArrayList<>();
        int keypos = 0;
        for (String layout : LAYOUT_NAMES) {
            Integer key = keypos < LAYOUT_KEYS.length ? LAYOUT_KEYS[keypos] : null;
            actions.add(new LoadLayoutAction(mainWindow, layout, key));
            keypos++;
        }
        keypos = 0;
        for (String layout : LAYOUT_NAMES) {
            Integer key = keypos < LAYOUT_KEYS.length ? LAYOUT_KEYS[keypos] : null;
            actions.add(new SaveLayoutAction(mainWindow, layout, key));
            keypos++;
        }
        actions.add(new ResetLayoutAction(mainWindow));
        return actions;
    }
}


final class SaveLayoutAction extends MainWindowAction {
    private static final long serialVersionUID = -2646217961498111734L;
    private final String layoutName;

    SaveLayoutAction(MainWindow mainWindow, String name, Integer key) {
        super(mainWindow);
        this.layoutName = name;
        setName("Save " + name);
        setIcon(IconFactory.saveFile(MainWindow.TOOLBAR_ICON_SIZE));
        setMenuPath("View.Layout");
        if (key != null) {
            setAcceleratorKey(KeyStroke.getKeyStroke(key,
                KeyStrokeManager.SHORTCUT_KEY_MASK | InputEvent.SHIFT_DOWN_MASK));
        }
        KeyStrokeManager.lookupAndOverride(this, getClass().getName() + "$" + layoutName);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        mainWindow.getDockControl().save(layoutName);
        mainWindow.setStatusLine("Layout saved to " + layoutName);
    }
}


final class LoadLayoutAction extends MainWindowAction {
    private static final long serialVersionUID = 3378477658914832831L;
    private final String layoutName;

    LoadLayoutAction(MainWindow mainWindow, String name, Integer key) {
        super(mainWindow);
        this.layoutName = name;
        setName("Load " + name);
        setIcon(IconFactory.openKeYFile(MainWindow.TOOLBAR_ICON_SIZE));
        if (key != null) {
            setAcceleratorKey(KeyStroke.getKeyStroke(key, InputEvent.CTRL_DOWN_MASK));
        }
        KeyStrokeManager.lookupAndOverride(this, getClass().getName() + "$" + layoutName);
        setMenuPath("View.Layout");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean defaultLayoutDefined =
            Arrays.asList(mainWindow.getDockControl().layouts()).contains(layoutName);
        if (defaultLayoutDefined) {
            mainWindow.getDockControl().load(layoutName);
            mainWindow.setStatusLine("Layout loaded from " + layoutName);
        } else {
            mainWindow.setStatusLine("Layout " + layoutName + " could not be found.");
        }
    }
}


final class ResetLayoutAction extends MainWindowAction {
    private static final long serialVersionUID = 8772915552504055750L;

    ResetLayoutAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Reset Layout");
        KeyStrokeManager.lookupAndOverride(this);
        setPriority(10);
        setMenuPath("View.Layout");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        DockingHelper.restoreFactoryDefault(mainWindow);
        mainWindow.setStatusLine("Factory reset of the layout.");
    }
}
