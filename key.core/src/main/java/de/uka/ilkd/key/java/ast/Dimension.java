/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast;

public class Dimension {

    private final int dim;

    public Dimension(int dim) {
        this.dim = dim;
    }

    public int getDimension() {
        return dim;
    }

}
