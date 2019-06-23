package de.uka.ilkd.key.gui.ext;

import java.util.EnumSet;
import java.util.List;

import javax.swing.Action;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.nodeviews.TacletMenu;
import de.uka.ilkd.key.gui.nodeviews.InnerNodeViewMenu;
import de.uka.ilkd.key.gui.nodeviews.SequentViewMenu;
import de.uka.ilkd.key.pp.PosInSequent;

/**
 * @author Alexander Weigl <weigl@kit.edu>
 * @author lanzinger
 */
public interface KeYSequentViewMenuExtension {
    /**
     * @param mainWindow non-null
     * @param pos the position which the user selected
     * @return a list of actions
     */
    List<Action> getSequentViewMenuActions(MainWindow mainWindow, PosInSequent pos);

    /**
     * @return the set of sequent view types for which this menu should be shown.
     */
    EnumSet<SequentViewMenuType> getSequentViewMenuTypes();

    /**
     * Contains an instance for every type of {@link SequentViewMenu} on which a
     * {@code KeYTermMenuExtension} may be shown.
     */
    @SuppressWarnings("rawtypes")
    public enum SequentViewMenuType {

        /** @see CurrentGoalViewMenu */
        CURRENT_GOAL_VIEW(TacletMenu.class),

        /** @see InnerNodeViewMenu */
        INNER_NODE_VIEW(InnerNodeViewMenu.class);

        private Class<? extends SequentViewMenu> clazz;

        private SequentViewMenuType(Class<? extends SequentViewMenu> clazz) {
            this.clazz = clazz;
        }

        /**
         * @return the subtype of {@link SequentViewMenu} corresponding to this instance.
         */
        public Class<? extends SequentViewMenu> getType() {
            return clazz;
        }

        /**
         * @param clazz a valid subtype of {@link SequentViewMenu} corresponding to this instance.
         * @return the corresponding instance.
         */
        public static SequentViewMenuType of(Class<? extends SequentViewMenu> clazz) {
            if (clazz.equals(TacletMenu.class)) {
                return CURRENT_GOAL_VIEW;
            } else if (clazz.equals(InnerNodeViewMenu.class)) {
                return INNER_NODE_VIEW;
            } else {
                return null;
            }
        }
    }
}
