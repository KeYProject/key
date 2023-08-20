/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.EventObject;

/** this class represents a Model event */
public class ModelEvent extends EventObject {

    /**
     *
     */
    private static final long serialVersionUID = -4505191823576266011L;

    public ModelEvent(Object source) {
        super(source);
    }

}
