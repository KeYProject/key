// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.


package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.image.BufferedImage;

import javax.swing.Icon;
import javax.swing.plaf.metal.MetalIconFactory.TreeControlIcon;

class KeYControlIcon extends TreeControlIcon {

    private static final Icon collapsedIcon   = new KeYControlIcon(true);
    private static final Icon expandedIcon    = new KeYControlIcon(false);

    private boolean collapsed;

    public static Icon getKeYCollapsedIcon() {
	return collapsedIcon;
    }

    public static Icon getKeYExpandedIcon() {
	return expandedIcon;
    }

    public KeYControlIcon ( boolean collapsed ) {
	super( collapsed );
	this.collapsed = collapsed;
	
    }

    public void paintIcon(Component c, Graphics g, int x, int y) {
	GraphicsConfiguration gc = c.getGraphicsConfiguration();
	Image image;
	if (gc != null) {
	    image = gc.createCompatibleImage(getIconWidth(), 
					     getIconHeight(),
					     Transparency.BITMASK);
	} else {
	    image = new BufferedImage(getIconWidth(),
				      getIconHeight(),
				      BufferedImage.TYPE_INT_ARGB);
	}
	Graphics imageG = image.getGraphics();		
	paintMe(c,imageG);
	imageG.dispose();
	
	g.drawImage(image, x, y, null);
    }

    private void paintMe(Component c, Graphics g) {
	// Draw tab top
	g.setColor(c.getBackground());
	g.fillRect(0,0,getIconWidth(), getIconHeight());

	int midx = getIconWidth() / 2;
	int midy = getIconHeight() / 2;

	int min = getIconWidth() < getIconHeight() ? 
	    getIconWidth() : getIconHeight();


	g.setColor(c.getGraphics().getColor());
	g.drawRect(midx-(min/4), midy-(min/4), (min/2)-1, (min/2)-1);

	g.drawLine(midx-(min/4 - 2), midy ,
		   midx+(min/4 - 2), midy);
	if (collapsed) {
	g.drawLine(midx, midy -(min/4 - 2),
		   midx, midy +(min/4 - 2));	    
	}
    }
}
