package de.uka.ilkd.key.gui.fonticons;

import javax.swing.*;

public enum KeYIcons {
    PROOF_SEARCH_STRATEGY_ICON, PROOF, EXPORT_MU_SCRIPT,
    EXPORT_MU_SCRIPT_CLIPBOARD, INTERLOG_LOAD, INTERLOG_SAVE,
    INTERLOG_ADD_USER_NOTE, INTERLOG_TOGGLE_FAV, JUMP_INTO_TREE,
    INTERLOG_TRY_APPLY, INTERLOG_EXPORT_KPS, EXPORT_MARKDOWN,
    INTERLOW_EXTENDED_ACTIONS, INTERLOG_RESUME, INTERLOG_PAUSE, INTERLOG_ICON, HEATMAP_DEACTIVATE, HEATMAP_ACTIVATE, INFO_VIEW_ICON;

    public Icon getIcon() {
        return UIManager.getIcon(this);
    }

    void setIcon(Icon icon) {
        UIManager.getDefaults().put(this, icon);
    }
}