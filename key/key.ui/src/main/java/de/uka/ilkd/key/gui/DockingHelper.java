package de.uka.ilkd.key.gui;

import bibliothek.gui.dock.common.CControl;
import bibliothek.gui.dock.common.DefaultSingleCDockable;
import bibliothek.gui.dock.common.action.CAction;
import bibliothek.gui.dock.common.action.CButton;
import bibliothek.gui.dock.common.intern.CDockable;
import bibliothek.gui.dock.util.IconManager;
import bibliothek.gui.dock.util.Priority;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeRegular;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;

import javax.swing.*;

/**
 * @author Alexander Weigl
 * @version 1 (15.05.19)
 */
public final class DockingHelper {
    public static float SIZE_ICON_DOCK = 12f;

    static CDockable createDock(TabPanel p) {
        CAction[] actions =
                p.getTitleActions().stream().map(DockingHelper::translateAction)
                        .toArray(CAction[]::new);

        return new DefaultSingleCDockable(p.getTitle(), p.getIcon(), p.getTitle(), p.getComponent(),
                p.getPermissions(), actions);
    }

    static CAction translateAction(Action action) {
        CButton button = new CButton(
                (String) action.getValue(Action.NAME),
                (Icon) action.getValue(Action.SMALL_ICON));
        button.addActionListener(action);
        button.setTooltip((String) action.getValue(Action.SHORT_DESCRIPTION));
        button.setEnabled(action.isEnabled());

        action.addPropertyChangeListener(evt -> {
            button.setText((String) action.getValue(Action.NAME));
            button.setIcon((Icon) action.getValue(Action.SMALL_ICON));
            button.setTooltip((String) action.getValue(Action.SHORT_DESCRIPTION));
            button.setEnabled(action.isEnabled());
        });

        return button;
    }

    public static void configure(CControl globalPort) {
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
                IconFontSwing.buildIcon(FontAwesomeSolid.MOUSE_POINTER, SIZE_ICON_DOCK));

        icons.setIcon("locationmanager.unmaximize_externalized", p,
                IconFontSwing.buildIcon(FontAwesomeSolid.EXTERNAL_LINK_ALT, SIZE_ICON_DOCK));

        icons.setIcon("screen.maximize", p,
                IconFontSwing.buildIcon(FontAwesomeRegular.EDIT, SIZE_ICON_DOCK));

        icons.setIcon("close", p,
                IconFontSwing.buildIcon(FontAwesomeRegular.WINDOW_CLOSE, SIZE_ICON_DOCK));

//            setIcon("replace", p,
//                    IconFontSwing.buildIcon(FontAwesomeRegular., 12f))
    }
}
