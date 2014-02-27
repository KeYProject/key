// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.gui;

import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.GraphicsConfiguration;
import java.awt.Image;
import java.awt.Transparency;
import java.awt.image.BufferedImage;

import javax.swing.Icon;
import javax.swing.ImageIcon;
import javax.swing.plaf.metal.MetalIconFactory.FolderIcon16;
import javax.swing.plaf.metal.MetalIconFactory.TreeControlIcon;
import javax.swing.plaf.metal.MetalLookAndFeel;

import de.uka.ilkd.key.util.KeYResourceManager;

public class IconFactory {

    private IconFactory() {}

    static KeYResourceManager resManager = KeYResourceManager.getManager();

    private static Image keyHole             = getImage("images/ekey-mono.gif");
    private static Image keyHoleAlmostClosed = getImage("images/ekey-brackets.gif");
    private static Image keyHoleClosed       = getImage("images/keyproved.gif");
    private static Image keyHoleInteractive     = getImage("images/keyinteractive.gif");
    private static Image keyLogo             = getImage("images/key-color.gif");
    private static Image keyLogo22 = getImage("images/key22.gif");
    private static Image keyLogoSmall        = getImage("images/key-color-icon-square.png");
    private static Icon provedFolderIcon     = KeYFolderIcon.getKeYFolderIconClosed();
    private static Icon closableFolderIcon   = KeYFolderIcon.getKeYFolderIconClosable();
    
    private static Image oneStepSimplifier = getImage("images/toolbar/oneStepSimplifier.png"); 

    private static Icon expandedIcon   = KeYControlIcon.getKeYExpandedIcon();
    private static Icon collapsedIcon  = KeYControlIcon.getKeYCollapsedIcon();

    private static Image prune		= getImage("images/toolbar/pruneProof.png");
    private static Image goalBack = getImage("images/toolbar/goalBack.png");
    private static Image autoModeStart =
        getImage("images/toolbar/autoModeStart.png");
    private static Image autoModeStop =
        getImage("images/toolbar/autoModeStop.png");
    private static Image decisionProcedureConfigArrow = 
	    getImage("images/toolbar/decProcArrow.png");

    private static Image junit = getImage("images/toolbar/junit_logo.png");
    private static Image jml   = getImage("images/toolbar/jml.png");
    private static Image uml   = getImage("images/toolbar/uml.png");

    private static Image openKeYFile = 
        getImage("images/toolbar/open.png");
    private static Image openMostRecentKeYFile = 
        getImage("images/toolbar/openMostRecent.png");
    private static Image saveFile = 
        getImage("images/toolbar/saveFile.png");
    private static Image editFile = 
        getImage("images/toolbar/edit.png");    
    private static Image abandonProof = getImage("images/toolbar/abandon.png");
    private static Image configure = getImage("images/toolbar/config.png");
    private static Image help = getImage("images/toolbar/help.png");
    private static Image proofMgt = getImage("images/toolbar/mgt.png");
    private static Image properties = getImage("images/toolbar/properties.png");
    private static Image quit = getImage("images/toolbar/quit.png");
    private static Image recentFiles = getImage("images/toolbar/recent.png");
    private static Image search = getImage("images/toolbar/search.png");
    private static Image search2 = getImage("images/toolbar/search2.png");
    private static Image statistics = getImage("images/toolbar/statistics.png");
    private static Image toolbox = getImage("images/toolbar/toolbox.png");

    private static Image plus = getImage("images/toolbar/plus.png");
    private static Image minus = getImage("images/toolbar/minus.png");
    private static Image expandGoals = getImage("images/toolbar/expandGoals.png");

    private static Image next = getImage("images/toolbar/go-next.png");
    private static Image previous = getImage("images/toolbar/go-previous.png");
    private static Image stop = getImage("images/toolbar/stop.png");

    private static Image interactiveAppLogo = 
        getImage("images/interactiveAppLogo.png");


    public static Image getImage(String s) {
	ImageIcon ii=resManager.createImageIcon(IconFactory.class, s);
	return ii.getImage();
    }

    public static ImageIcon scaleIcon(Image im, int x, int y) {
	Image scaledim=im.getScaledInstance(x,y,Image.SCALE_SMOOTH);
	return new ImageIcon(scaledim);
    }

    public static ImageIcon abandon(int x) {
        return scaleIcon(abandonProof ,x,x);
    }

    public static ImageIcon configure (int x) {
        return scaleIcon(configure ,x,x);
    }

    public static ImageIcon help (int x) {
        return scaleIcon(help ,x,x);
    }

    public static ImageIcon proofMgt (int x) {
        return scaleIcon(proofMgt ,x,x);
    }

    public static ImageIcon properties (int x) {
        return scaleIcon(properties ,x,x);
    }

    public static ImageIcon quit (int x) {
        return scaleIcon(quit ,x,x);
    }

    public static ImageIcon recentFiles (int x) {
        return scaleIcon(recentFiles ,x,x);
    }

    public static ImageIcon search (int x) {
        return scaleIcon(search ,x,x);
    }

    public static ImageIcon search2 (int x) {
        return scaleIcon(search2 ,x,x);
    }

    public static ImageIcon statistics(int x) {
        return scaleIcon(statistics,x,x);
    }


    public static ImageIcon toolbox(int x) {
        return scaleIcon(toolbox,x,x);
    }


    public static ImageIcon plus(int x) {
        return scaleIcon(plus,x,x);
    }

    public static ImageIcon minus(int x) {
        return scaleIcon(minus,x,x);
    }

    public static ImageIcon expandGoals(int x) {
        return scaleIcon(expandGoals,x,x);
    }

    public static ImageIcon next(int x) {
        return scaleIcon(next,x,x);
    }

    public static ImageIcon previous(int x) {
        return scaleIcon(previous,x,x);
    }


    public static ImageIcon stop(int x) {
        return scaleIcon(stop,x,x);
    }


    public static ImageIcon keyHole(int x, int y) {
	return scaleIcon(keyHole,x,y);
    }
    
    public static ImageIcon keyHoleClosed(int x, int y) {
	return scaleIcon(keyHoleClosed,x,y);
    }

    public static ImageIcon keyHoleAlmostClosed(int x, int y) {
	return scaleIcon(keyHoleAlmostClosed,x,y);
    }
    
    public static ImageIcon keyHoleInteractive(int x, int y) {
        return scaleIcon(keyHoleInteractive,x,y);
    }
    
    public static ImageIcon keyLogo(int x, int y) {
	return  scaleIcon(keyLogo,x,y);
    }
 
    public static ImageIcon key22Logo(int x, int y) {
	return  scaleIcon(keyLogo22,x,y);
    }

    @Deprecated
    public static ImageIcon reuseLogo() {
	return null;
    }

    @Deprecated
    public static ImageIcon resumeLogo(int size) {
	return null;
    }

    @Deprecated
    public static ImageIcon resumeDisabledLogo(int size) {
	return null;
    }

    public static ImageIcon autoModeStartLogo(int size) {
        return scaleIcon(autoModeStart, size, size);
    }

    public static ImageIcon autoModeStopLogo(int size) {
        return scaleIcon(autoModeStop, size, size);
    }

    @Deprecated
    public static ImageIcon selectStrategyArrow(int size) {
        return null;
    }
    
    public static ImageIcon selectDecProcArrow(int size) {
        return scaleIcon(decisionProcedureConfigArrow, size / 2, size);
    }
    
    public static Icon oneStepSimplifier(int size) {
        return scaleIcon(oneStepSimplifier, size, size);
    }

    public static ImageIcon junitLogo(int size) {
	return scaleIcon(junit, size, size);
    }
    
    public static ImageIcon jmlLogo(int size) {
        return scaleIcon(jml, size, size);
    }
    
    public static ImageIcon umlLogo(int size) {
        return scaleIcon(uml, size, size);
    }
    
    public static ImageIcon pruneLogo(int size) {
    	return scaleIcon(prune, size, size);
    }

    public static ImageIcon goalBackLogo(int size) {
	return scaleIcon(goalBack, size, size);
    }

    public static Icon provedFolderIcon() {
	return provedFolderIcon;
    }
    
    public static Icon closableFolderIcon() {
	return closableFolderIcon;
    }


    public static Icon expandedIcon() {
	return expandedIcon;
    }
    
    public static Icon collapsedIcon() {
	return collapsedIcon;
    }

    public static Image keyLogo() {
	return keyLogoSmall;
    }

    public static Icon openMostRecent(int size) {       
        return scaleIcon(openMostRecentKeYFile, size, size);
    }

    public static Icon openKeYFile(int size) {       
        return scaleIcon(openKeYFile, size, size);
    }

    public static Icon saveFile(int size) {       
        return scaleIcon(saveFile, size, size);
    }
    
    public static Icon editFile(int size) {       
        return scaleIcon(editFile, size, size);
    }    

    public static Icon interactiveAppLogo(int size) {       
       return scaleIcon(interactiveAppLogo, size, size);
    }


    public static class KeYFolderIcon extends FolderIcon16 {

        private static final long serialVersionUID = 5120051888984645985L;
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
            GraphicsConfiguration gc = c != null ? c.getGraphicsConfiguration() : null;
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

    private static class KeYControlIcon extends TreeControlIcon {

        private static final long serialVersionUID = -929097387090481643L;
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
}
