// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
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
import javax.swing.plaf.metal.MetalLookAndFeel;
import javax.swing.plaf.metal.MetalIconFactory.FolderIcon16;

class KeYFolderIcon extends FolderIcon16 {

    private static final Icon closedIcon   = new KeYFolderIcon(Color.green.darker());
    private static final Icon closableIcon = new KeYFolderIcon(Color.blue.darker());
    private static final Dimension folderIcon16Size = new Dimension( 16, 16 );

    private final Color frontColor;

    public static Icon getKeYFolderIconClosed() {
	return closedIcon;
    }

    public static Icon getKeYFolderIconClosable() {
	return closableIcon;
    }

    public KeYFolderIcon ( Color p_frontColor ) {
	frontColor = p_frontColor;
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
	
	g.drawImage(image, x, y+getShift(), null);
    }

    private void paintMe(Component c, Graphics g) {

	int right = folderIcon16Size.width - 1;
	int bottom = folderIcon16Size.height - 1;
      
	// Draw tab top
	g.setColor( MetalLookAndFeel.getPrimaryControlDarkShadow() );
	g.setColor(Color.green.darker().darker());
	g.drawLine( right - 5, 3, right, 3 );
	g.drawLine( right - 6, 4, right, 4 );

	// Draw folder front

	//g.setColor( MetalLookAndFeel.getPrimaryControl() );
	g.setColor(frontColor);
	g.fillRect( 2, 7, 13, 8 );

	// Draw tab bottom
	g.setColor( MetalLookAndFeel.getPrimaryControlShadow() );
	g.drawLine( right - 6, 5, right - 1, 5 );

	// Draw outline
	g.setColor( MetalLookAndFeel.getPrimaryControlInfo() );
	g.drawLine( 0, 6, 0, bottom );            // left side
	g.drawLine( 1, 5, right - 7, 5 );         // first part of top
	g.drawLine( right - 6, 6, right - 1, 6 ); // second part of top
	g.drawLine( right, 5, right, bottom );    // right side
	g.drawLine( 0, bottom, right, bottom );   // bottom

	// Draw highlight
	g.setColor( MetalLookAndFeel.getPrimaryControlHighlight() );
	g.drawLine( 1, 6, 1, bottom - 1 );
	g.drawLine( 1, 6, right - 7, 6 );
	g.drawLine( right - 6, 7, right - 1, 7 );

    }

    public int getShift() { return -1; }
    public int getAdditionalHeight() { return 2; }

    public int getIconWidth() { return folderIcon16Size.width; }
    public int getIconHeight() { return folderIcon16Size.height + getAdditionalHeight(); }
}
