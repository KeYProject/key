package de.uka.ilkd.key.gui.docking;

import bibliothek.gui.Dockable;
import bibliothek.gui.dock.action.ActionType;
import bibliothek.gui.dock.action.DockActionSource;
import bibliothek.gui.dock.action.MenuDockAction;
import bibliothek.gui.dock.action.actions.SimpleDockAction;
import bibliothek.gui.dock.action.view.ActionViewConverter;
import bibliothek.gui.dock.action.view.ViewTarget;
import bibliothek.gui.dock.common.action.CAction;
import bibliothek.gui.dock.common.action.CMenu;
import bibliothek.gui.dock.common.action.core.CommonDecoratableDockAction;
import bibliothek.gui.dock.common.intern.action.CDecorateableAction;

import javax.swing.*;
import java.util.function.Supplier;

public class DynamicCMenu extends CDecorateableAction<DynamicCMenu.Action> {
    public DynamicCMenu(Supplier<CMenu> supplier) {
        super(null);
        this.init(new Action(this, supplier));
    }

    public DynamicCMenu(String text, Icon icon, Supplier<CMenu> supplier) {
        this(supplier);
        this.setText(text);
        this.setIcon(icon);
    }

    public static class Action extends SimpleDockAction
            implements MenuDockAction, CommonDecoratableDockAction {
        private final CAction action;
        private final Supplier<CMenu> supplier;

        public Action(CAction action, Supplier<CMenu> supplier) {
            super(true);
            this.action = action;
            this.supplier = supplier;
        }

        @Override
        public DockActionSource getMenu(Dockable dockable) {
            return supplier.get().intern().getMenu(dockable);
        }

        public <V> V createView(ViewTarget<V> target, ActionViewConverter converter,
                Dockable dockable) {
            return converter.createView(ActionType.MENU, this, target, dockable);
        }

        public boolean trigger(Dockable dockable) {
            return false;
        }

        public CAction getAction() {
            return this.action;
        }
    }
}
