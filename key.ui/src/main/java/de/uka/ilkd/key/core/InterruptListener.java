/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.core;

import java.util.EventListener;

/**
 * Event listener for interruptions. These are triggered when the user clicks on the stop button.
 */
public interface InterruptListener extends EventListener {

    void interruptionPerformed();

}
