/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.docking;

import org.key_project.dockingframes.common.common.action.CAction;
import org.key_project.dockingframes.common.common.action.CMenu;
import org.key_project.dockingframes.common.common.action.core.CommonDecoratableDockAction;
import org.key_project.dockingframes.common.common.intern.action.CDecorateableAction;
import org.key_project.dockingframes.core.gui.Dockable;
import org.key_project.dockingframes.core.gui.dock.action.ActionType;
import org.key_project.dockingframes.core.gui.dock.action.DockActionSource;
import org.key_project.dockingframes.core.gui.dock.action.MenuDockAction;
import org.key_project.dockingframes.core.gui.dock.action.actions.SimpleDockAction;
import org.key_project.dockingframes.core.gui.dock.action.view.ActionViewConverter;
import org.key_project.dockingframes.core.gui.dock.action.view.ViewTarget;

import java.util.function.Supplier;
import javax.swing.*;


/**
 * CMenu that gets (re-)generated when the action gets fired using the provided supplier.
 * The generated CMenu behaves just like a normal CMenu (same positioning, content, etc.).
 * The {@link DynamicCMenu} can be styled like other actions.
 *
 * @author Julian Wiesler
 */
public class DynamicCMenu extends CDecorateableAction<DynamicCMenu.Action> {
    /**
     * constructor
     *
     * @param supplier the supplier
     */
    public DynamicCMenu(Supplier<CMenu> supplier) {
        super(null);
        this.init(new Action(this, supplier));
    }

    /**
     * constructor
     *
     * @param text the text of this action
     * @param icon the icon of this action
     * @param supplier the supplier
     */
    public DynamicCMenu(String text, Icon icon, Supplier<CMenu> supplier) {
        this(supplier);
        this.setText(text);
        this.setIcon(icon);
    }

    /**
     * Action that implements the dynamic behaviour and calls the supplier
     * This class need not be instantiated manually, it is only public because it is contained in
     * the
     * generics of the surrounding class.
     **/
    public static class Action extends SimpleDockAction
            implements MenuDockAction, CommonDecoratableDockAction {
        /** associated action */
        private final CAction action;
        /** the supplier */
        private final Supplier<CMenu> supplier;

        /** constructor */
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
