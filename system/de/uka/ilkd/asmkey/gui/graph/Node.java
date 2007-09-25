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

import java.awt.geom.Point2D;

/**
 * This class is the abstract class responsible
 * to draw nodes in the {@link ArcsComponent}.
 */
public abstract class Node {

    public abstract Point2D topPoint4Edge();
    
    public abstract Point2D leftPoint4Edge();

    public abstract Point2D bottomPoint4Edge();

    public abstract Point2D rightPoint4Edge();

}
