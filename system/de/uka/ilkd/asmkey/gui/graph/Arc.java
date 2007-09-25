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
 * This class represents an Arc
 * @see ArcsRenderer
 * @author Stanislas Nanchen
 */
public class Arc {
    
    private Point2D startPoint;

    private int height;
    private int length;


    public Arc(Point2D startPoint, int height, int length) {
	this.startPoint = startPoint;
	this.height = height;
	this.length = length;
    }

    public Point2D startPoint() {
	return startPoint;
    }

    public int height() {
	return height;
    }
    
    public int length() {
	return length;
    }
   
}
