// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.gui.graph;

/**
 * this class contains some static constants.
 * it is name to give credit to the origin of this
 * representation.
 * it contains also the placement algorithm and edge in cell
 * algorithm.
 * @see CellRenderer
 * @author Stanislas Nanchen
 */
public class ThreadArcs {

    /**
     * in the horizontal mode, a positive height draws the
     * path above and a negative height draws the path down.
     */
    public static int HORIZONTAL = 0;

    /**
     * in the vertical mode, a positive height draws the
     * path on the left and a negative height draws the
     * path on the right.
     */
    public static int VERTICAL = 1;

}
