/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof;

/** this exception thrown if an if-sequent match failed */
public class IfMismatchException extends SVInstantiationException {

    /**
     *
     */
    private static final long serialVersionUID = 933425921270034135L;

    public IfMismatchException(String description) {
        super(description);
    }


}
