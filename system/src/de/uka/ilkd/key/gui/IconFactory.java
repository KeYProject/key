// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;

import java.awt.Image;

import javax.swing.Icon;
import javax.swing.ImageIcon;

import de.uka.ilkd.key.util.KeYResourceManager;

public class IconFactory {

    private IconFactory() {}

    static KeYResourceManager resManager = KeYResourceManager.getManager();

    private static Image keyHole             = getImage("images/ekey-mono.gif");
    private static Image keyHoleAlmostClosed = getImage("images/ekey-brackets.gif");
    private static Image keyHoleClosed       = getImage("images/keyproved.gif");
    private static Image keyHoleInteractive     = getImage("images/keyinteractive.gif");
    private static Image keyLogo             = getImage("images/key-color.gif");
    private static Image keyLogoSmall        = getImage("images/key-color-icon-square.png");
    private static Icon provedFolderIcon     = KeYFolderIcon.getKeYFolderIconClosed();
    private static Icon closableFolderIcon   = KeYFolderIcon.getKeYFolderIconClosable();

    private static Icon expandedIcon   = KeYControlIcon.getKeYExpandedIcon();
    private static Icon collapsedIcon  = KeYControlIcon.getKeYCollapsedIcon();

    private static Image reuse    = getImage("images/toolbar/ff.gif");
    private static Image goalBack = getImage("images/toolbar/goalBack.png");
    private static Image autoResume = getImage("images/toolbar/autoResume.png");
    private static Image autoResumeDisabled = 
	getImage("images/toolbar/autoResumeDisabled.png");
    private static Image autoModeStart =
        getImage("images/toolbar/autoModeStart.png");
    private static Image autoModeStop =
        getImage("images/toolbar/autoModeStop.png");
    private static Image autoModeConfigArrow = 
    getImage("images/toolbar/autoModeConfigArrow.png");
    private static Image decisionProcedureICS = 
	getImage("images/toolbar/decisionProcedureICS.png");
    private static Image decisionProcedureSimplify = 
	getImage("images/toolbar/decisionProcedureSimplify.png");
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
        getImage("images/toolbar/editFile.gif");    

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

    public static ImageIcon reuseLogo() {
	return scaleIcon(reuse, 15, 15);
    }

    public static ImageIcon resumeLogo(int size) {
	return scaleIcon(autoResume, size, size);
    }

    public static ImageIcon resumeDisabledLogo(int size) {
	return scaleIcon(autoResumeDisabled, size, size);
    }

    public static ImageIcon autoModeStartLogo(int size) {
        return scaleIcon(autoModeStart, size, size);
    }

    public static ImageIcon autoModeStopLogo(int size) {
        return scaleIcon(autoModeStop, size, size);
    }

    public static ImageIcon selectStrategyArrow(int size) {
        return scaleIcon(autoModeConfigArrow, size / 2, size);
    }
    
    public static ImageIcon selectDecProcArrow(int size) {
        return scaleIcon(decisionProcedureConfigArrow, size / 2, size);
    }

    public static ImageIcon simplifyLogo(int size) {
	return scaleIcon(decisionProcedureSimplify, size, size);
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

    public static ImageIcon icsLogo(int size) {
	return scaleIcon(decisionProcedureICS, size, size);
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

}
