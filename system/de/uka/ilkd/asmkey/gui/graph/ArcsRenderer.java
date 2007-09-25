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

import java.awt.geom.GeneralPath;

/**
 * This class is the class responsible
 * to draw the cells with the arcs and the nodes
 * in the {@link ArcsList} and {@link ArcsTable}
 * cf. article on this.
 *
 * @author Stanislas Nanchen
 */
public class ArcsRenderer {

    private int direction;
    
    /** the smaller radius for 
     * the circles, in int. the width
     * of a cell is 2*radius;
     */
    private int radius;

    public ArcsRenderer(int direction, int radius) {
	setDirection(direction);
	setRadius(radius);
    }

    public void setDirection(int direction) {
	this.direction = direction;
    }

    public int direction() {
	return direction;
    }
    
    public void setRadius(int radius) {
	this.radius = radius;
    }

    public int radius() {
	return radius;
    }

    private GeneralPath pathForArc(Arc arc) {
	/**
	 * we always draw from left to right and
	 * from top to bottom.
	 */
	int absHeight;
	boolean negative;
	GeneralPath path = new GeneralPath();
	float startX, startY, controlX, controlY, endX, endY;
	
	absHeight = StrictMath.abs(arc.height());
	negative = (arc.height()<0)?true:false;
	startX = (float) arc.startPoint().getX();
	startY = (float) arc.startPoint().getY();
	path.moveTo(startX, startY);
	
	/** if the absHeight is greater that the length, we would need
	 * to draw an ellipse, so we reduce the height.
	 * note: the placement algorithm never generates such an arc.
	 */
	if (absHeight > arc.length()) {
	    absHeight = arc.length();
	}
	
	/**
	 * the height 0 is a special case.
	 */
	if(absHeight == 0) {
	    /**
	     * if the height is 0, the length must be 1 and we have a line.
	     */
	    if (direction == ThreadArcs.HORIZONTAL) {
		/* if horizontal, then move the X coord on the right */
		endX = startX + 2*radius;
		endY = startY;
	    } else { // ThreadArcs.VERTICAL
		/* if vertical, then move the Y coord down */
		endX = startX;
		endY = startY + 2* radius;
	    }
	    /* trace the line */
	    path.lineTo(endX, endY);
	} else {
	    /* in the general, case, we have a path made of 2 or 3 strokes:
		 * - a quarter of circle.
		 * - a optinal line.
		 * - a quarter of circle.
		 */
	    if (direction == ThreadArcs.HORIZONTAL) {
		/* if we are horizontal, the control point is down
		 * or up of radius amount depending on relative height.
		 */
		controlX = startX;
		controlY = startY + radius*absHeight*(negative?1:-1);
		/* the end point is on the right by radius amount */
		endX = controlX + radius*absHeight;
		endY = controlY;
	    } else { // ThreadArcs.VERTICAL
		/* if we are vertical, the control point is left or
		 * right of radius amount depending on relative height.
		 */
		controlX = startX + radius*absHeight*(negative?1:-1);
		controlY = startY;
		/* the end point is down by radius amount */
		endX = controlX;
		endY = controlY + radius*absHeight;
	    }
	    /* we draw the first circle */
	    path.quadTo(controlX, controlY, endX, endY);
	    /* if necessary, we draw a line */
	    if (absHeight < arc.length()) {
		float distance = (arc.length() - absHeight) * radius;
		if (direction == ThreadArcs.HORIZONTAL) {
		    /* if horizontal, we go right */
		    endX = endX + distance;
		} else { // ThreadArcs.VERTICAL
		    /* if vertical, we go down */
		    endY = endY + distance;
		}
		path.lineTo(endX, endY);
	    }
	    if (direction == ThreadArcs.HORIZONTAL) {
		/* if we are horizontal, the control point is
		 * the end point shift to the right
		 */
		controlX = endX + radius*absHeight;
		controlY = endY;
		/* the end point goes back on the startY */
		endX = controlX;
		endY = startY;
	    } else { // ThreadArcs.VERTICAL
		/* if we are vertical, the control point is
		 * the end point shifted down */
		controlX = endX;
		controlY = endY + radius*absHeight;
		/* the end point goes back on the startX */
		endX = startX;
		endY = controlY;
	    }
	    /* we can draw the second circle */
	    path.quadTo(controlX, controlY, endX, endY);
	}
	/* we are finished */
	return path;
    }

   


}
