package de.uka.ilkd.key.gui.docking;

import bibliothek.gui.dock.common.DefaultSingleCDockable;
import bibliothek.gui.dock.common.action.CAction;
import bibliothek.gui.dock.common.action.CButton;
import bibliothek.gui.dock.common.action.CCheckBox;
import bibliothek.gui.dock.common.intern.CDockable;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import org.jetbrains.annotations.NotNull;

import javax.swing.*;
import java.util.stream.Stream;

public class DockingHelper {
    public static @NotNull CDockable createDock(@NotNull TabPanel p) {
        Stream<CAction> actions = p.getTitleActions().stream().map(DockingHelper::translateAction);
        CAction[] a = Stream.concat(actions, p.getTitleCActions().stream()).toArray(CAction[]::new);

        return new DefaultSingleCDockable(p.getClass().getName(),
                p.getIcon(), p.getTitle(), p.getComponent(),
                p.getPermissions(), a);
    }

    public static @NotNull CAction translateAction(@NotNull Action action) {
        if (action.getValue(Action.SELECTED_KEY) != null) {
            return createCheckBox(action);

        } else {
            return createButton(action);
        }
    }

    private static @NotNull CAction createCheckBox(@NotNull Action action) {
        CCheckBox button = new CCheckBox(
                (String) action.getValue(Action.NAME),
                (Icon) action.getValue(Action.SMALL_ICON)) {
            @Override
            protected void changed() {
                action.putValue(Action.SELECTED_KEY, this.isSelected());
                action.actionPerformed(null);
            }
        };

        button.setTooltip((String) action.getValue(Action.SHORT_DESCRIPTION));
        button.setEnabled(action.isEnabled());
        button.setSelected(Boolean.TRUE == action.getValue(Action.SELECTED_KEY));
        action.addPropertyChangeListener(evt -> {
            button.setText((String) action.getValue(Action.NAME));
            button.setIcon((Icon) action.getValue(Action.SMALL_ICON));
            button.setTooltip((String) action.getValue(Action.SHORT_DESCRIPTION));
            button.setEnabled(action.isEnabled());
        });
        return button;
    }

    private static CAction createButton(Action action) {
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
}
