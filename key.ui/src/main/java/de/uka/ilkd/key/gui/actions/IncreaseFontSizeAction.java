/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.configuration.ConfigChangeEvent;
import de.uka.ilkd.key.gui.configuration.ConfigChangeListener;
import de.uka.ilkd.key.gui.fonticons.IconFactory;

import org.jspecify.annotations.NullMarked;

@NullMarked
public class IncreaseFontSizeAction extends MainWindowAction implements ConfigChangeListener {

    /**
     * generated sUID
     */
    private static final long serialVersionUID = 1670432514230642280L;

    /**
     * creates the action to increase the font size of the sequent and proof view
     *
     * @param mainWindow the main window
     */
    /**
     * The action-configuration setters and the {@link Config} listener registration below operate
     * on {@code this} while the receiver is still under initialization (EISOP initialization
     * check); safe here since these configure the local action only, suppressed with scoped keys.
     */
    @SuppressWarnings({ "nullness:method.invocation.invalid",
        "nullness:argument.type.incompatible" })
    public IncreaseFontSizeAction(MainWindow mainWindow) {
        super(mainWindow);

        setName("Larger");
        setIcon(IconFactory.plus(16));

        Config.DEFAULT.addConfigChangeListener(this);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        Config.DEFAULT.larger();
    }

    @Override
    public void configChanged(ConfigChangeEvent e) {
        setEnabled(!Config.DEFAULT.isMaximumSize());
    }

}
