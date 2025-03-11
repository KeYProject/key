/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.event.ActionListener;
import javax.swing.JMenu;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.rule.PosTacletApp;

import org.key_project.util.collection.ImmutableList;

/**
 * This simple taclet menu displays the user a list of applicable taclets and lets select her/him
 * one of those. It is similar to {@link de.uka.ilkd.key.gui.nodeviews.CurrentGoalViewMenu} but with
 * some important differences:
 * <ul>
 * <li>it returns the selected taclet app and does not initiate any further action as the original
 * {@link de.uka.ilkd.key.gui.nodeviews.CurrentGoalViewMenu}</li>
 * <li>it does not display any additional menu entries like: Apply strategies here, built-in rules,
 * abbreviation etc.</li>
 * </ul>
 */
public class SimpleTacletSelectionMenu extends JMenu {

    /**
     *
     */
    private static final long serialVersionUID = 3027934580300468044L;

    /**
     * creates an instance of this menu displaying the applications stored in <tt>apps</tt>
     *
     * @param apps the {@link ImmutableList<PosTacletApp>} to be displayed
     * @param info the NotationInfo used to pretty print the taclets in tooltips
     * @param listener the ActionListener which is registered at each menu item
     */
    public SimpleTacletSelectionMenu(ImmutableList<PosTacletApp> apps, NotationInfo info,
            ActionListener listener, Services services) {
        super("Select Rule to Apply");

        addMenuEntries(apps, info, listener, services);
    }

    /**
     * adds the given applications to the menu
     *
     * @param apps the IList to be displayed
     * @param info the NotationInfo used to pretty print the taclets in tooltips
     * @param listener the ActionListener which is registered at each menu item
     */
    private void addMenuEntries(ImmutableList<PosTacletApp> apps, NotationInfo info,
            ActionListener listener, Services services) {
        for (PosTacletApp app : apps) {
            final DefaultTacletMenuItem item = new DefaultTacletMenuItem(app, info, services);
            item.addActionListener(listener);
            add(item);
        }
    }
}
