/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;


import org.jspecify.annotations.Nullable;

/** thrown if a duplicate is being added via addUnique() */
public class NotUniqueException extends Exception {
    private final @Nullable Object offender;

    public NotUniqueException(@Nullable Object o) {
        offender = o;
    }

    @Override
    public String toString() {
        return "Tried to add a duplicate object to set. Offender is \n" + offender +
            (offender != null ? " of class " + offender.getClass() : "");
    }
}
