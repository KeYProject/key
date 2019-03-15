package de.uka.ilkd.key.gui.fonticons;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.MainWindowTabbedPane;

import java.awt.*;

/**
 * @author Alexander Weigl
 * @version 1 (15.03.19)
 */
public class KeYIconManagement {

    private static final float SMALL_ICON_SIZE = 12f;

    static {
        enableFontIcons();
    }

    public static void enableOldIcons() {
        KeYIcons.HEATMAP_ACTIVATE.setIcon(
                IconFontSwing.buildIcon(FontAwesomeSolid.FIRE_EXTINGUISHER, MainWindow.TOOLBAR_ICON_SIZE));
        KeYIcons.HEATMAP_DEACTIVATE.setIcon(
                IconFontSwing.buildIcon(FontAwesomeSolid.FIRE, MainWindow.TOOLBAR_ICON_SIZE));
    }

    public static void enableFontIcons() {
        KeYIcons.PROOF_SEARCH_STRATEGY_ICON.setIcon(
                IconFontSwing.buildIcon(FontAwesomeSolid.COGS, MainWindowTabbedPane.TAB_ICON_SIZE));

        KeYIcons.INFO_VIEW_ICON.setIcon(
                IconFontSwing.buildIcon(FontAwesomeSolid.INFO_CIRCLE, MainWindowTabbedPane.TAB_ICON_SIZE));

        KeYIcons.PROOF.setIcon(
                IconFontSwing.buildIcon(FontAwesomeSolid.TREE, MainWindowTabbedPane.TAB_ICON_SIZE));
        KeYIcons.EXPORT_MU_SCRIPT.setIcon(
                IconFontSwing.buildIcon(FontAwesomeSolid.FILE_EXPORT, SMALL_ICON_SIZE));
        KeYIcons.EXPORT_MU_SCRIPT_CLIPBOARD.setIcon(
                IconFontSwing.buildIcon(FontAwesomeRegular.COPY, SMALL_ICON_SIZE));
        KeYIcons.INTERLOG_LOAD.setIcon(
                IconFontSwing.buildIcon(FontAwesomeSolid.TRUCK_LOADING, SMALL_ICON_SIZE));
        KeYIcons.INTERLOG_SAVE.setIcon(
                IconFontSwing.buildIcon(FontAwesomeRegular.SAVE, SMALL_ICON_SIZE));
        KeYIcons.INTERLOG_ADD_USER_NOTE.setIcon(
                IconFontSwing.buildIcon(FontAwesomeRegular.STICKY_NOTE, SMALL_ICON_SIZE));
        KeYIcons.INTERLOG_TOGGLE_FAV.setIcon(
                IconFontSwing.buildIcon(FontAwesomeSolid.HEART, SMALL_ICON_SIZE, Color.red));
        KeYIcons.JUMP_INTO_TREE.setIcon(
                IconFontSwing.buildIcon(FontAwesomeRegular.TIRED, SMALL_ICON_SIZE));
        KeYIcons.INTERLOG_TRY_APPLY.setIcon(
                IconFontSwing.buildIcon(FontAwesomeRegular.MOON, SMALL_ICON_SIZE));
        KeYIcons.INTERLOG_EXPORT_KPS.setIcon(
                IconFontSwing.buildIcon(FontAwesomeSolid.CODE, SMALL_ICON_SIZE));
        KeYIcons.EXPORT_MARKDOWN.setIcon(IconFontSwing.buildIcon(
                FontAwesomeSolid.FILE_EXPORT, SMALL_ICON_SIZE));
        KeYIcons.INTERLOW_EXTENDED_ACTIONS.setIcon(
                IconFontSwing.buildIcon(FontAwesomeSolid.WRENCH, SMALL_ICON_SIZE));
        KeYIcons.INTERLOG_PAUSE.setIcon(
                IconFontSwing.buildIcon(FontAwesomeSolid.PAUSE_CIRCLE, SMALL_ICON_SIZE));
        KeYIcons.INTERLOG_RESUME.setIcon(
                IconFontSwing.buildIcon(FontAwesomeSolid.PLAY_CIRCLE, SMALL_ICON_SIZE));
        KeYIcons.INTERLOG_ICON.setIcon(
                IconFontSwing.buildIcon(FontAwesomeSolid.BOOK, MainWindowTabbedPane.TAB_ICON_SIZE));
        KeYIcons.HEATMAP_ACTIVATE.setIcon(
                IconFontSwing.buildIcon(FontAwesomeSolid.FIRE_EXTINGUISHER, MainWindow.TOOLBAR_ICON_SIZE));
        KeYIcons.HEATMAP_DEACTIVATE.setIcon(
                IconFontSwing.buildIcon(FontAwesomeSolid.FIRE, MainWindow.TOOLBAR_ICON_SIZE));
    }
}

