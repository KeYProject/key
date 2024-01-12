/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

/**
 * this interface is implemented by listener of change events of a model
 */

public interface ModelChangeListener {

    /** this method is called if the model has changed */
    void modelChanged(ModelEvent me);

}
