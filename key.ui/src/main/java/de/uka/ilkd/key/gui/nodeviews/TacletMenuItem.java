/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.event.ActionListener;

import de.uka.ilkd.key.rule.TacletApp;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This interface is implemented by items to be displayed in the @link TacletMenu.
 */
@NullMarked
interface TacletMenuItem {

    void addActionListener(ActionListener listener);

    /**
     * gets the Taclet that is attached to this item
     *
     * @return the attached Taclet
     */
    @Nullable
    TacletApp connectedTo();

}
