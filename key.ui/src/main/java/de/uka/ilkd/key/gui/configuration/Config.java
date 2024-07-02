// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.configuration;

import java.awt.Font;
import java.util.ArrayList;
import java.util.List;

import javax.swing.UIManager;

import de.uka.ilkd.key.settings.ProofIndependentSettings;

/** this class is used to set some default gui properties */
public class Config {

    /** name of different fonts */
    public static final String KEY_FONT_PROOF_TREE 
	= "KEY_FONT_PROOF_TREE";
    public static final String KEY_FONT_SEQUENT_VIEW 
	= "KEY_FONT_CURRENT_GOAL_VIEW";
    public static final String KEY_FONT_GOAL_LIST_VIEW 
	= "KEY_FONT_GOAL_LIST_VIEW";
    public static final String KEY_FONT_PROOF_LIST_VIEW 
	= "KEY_FONT_PROOF_LIST_VIEW";

    /** An array of font sizes for the goal view */
    public static final int[] SIZES = new int[]{10,12,14,17,20,24};

    public static final Config DEFAULT = new Config();
    
    /** The index of the current size */
    private int sizeIndex; 
    { 
        sizeIndex = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().sizeIndex();
        if (sizeIndex < 0 || sizeIndex > SIZES.length) {
            sizeIndex = 0;
        }
    }

    /** cached ConfigChange event */
    private ConfigChangeEvent configChangeEvent = 
	new ConfigChangeEvent(this);

    /** the listeners to this Config */
    private final List<ConfigChangeListener> listenerList =
        new ArrayList<ConfigChangeListener>(5);

    private Config() {
        setDefaultFonts();
    }

    public void larger() {
	if (!isMaximumSize()) {
	    sizeIndex++;
	    ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setFontIndex(sizeIndex);
//	    ProofSettings.DEFAULT_SETTINGS.getViewSettings().setFontIndex(sizeIndex);
	    setDefaultFonts();
	    fireConfigChange(); 
	}
    }

    public void smaller() {
	if (!isMinimumSize()) {
	    sizeIndex--;
	    ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setFontIndex(sizeIndex);
//	    ProofSettings.DEFAULT_SETTINGS.getViewSettings().setFontIndex(sizeIndex);
	    setDefaultFonts(); 
	    fireConfigChange();
	}
    }

    public boolean isMinimumSize() {
	return sizeIndex==0;
    }
    
    public boolean isMaximumSize() {
	return sizeIndex== SIZES.length-1;
    }

    public void setDefaultFonts() {
	UIManager.put(KEY_FONT_PROOF_TREE, 
		      new Font("Default", Font.PLAIN, SIZES[sizeIndex]));
	UIManager.put(KEY_FONT_SEQUENT_VIEW, 
		      new Font("Monospaced", Font.PLAIN, SIZES[sizeIndex]));
	UIManager.put(KEY_FONT_GOAL_LIST_VIEW, 
		      new Font("Default", Font.PLAIN, SIZES[2]));
	UIManager.put(KEY_FONT_PROOF_LIST_VIEW, 
		      new Font("Default", Font.PLAIN, SIZES[2]));
    }


    public void addConfigChangeListener(ConfigChangeListener listener) {
	synchronized(listenerList) {
	    listenerList.add(listener);	    
	}
    }

    public void removeConfigChangeListener(ConfigChangeListener listener) {
	synchronized(listenerList) {
	    listenerList.remove(listener);
	}
    }		

    public synchronized void fireConfigChange() {
	synchronized(listenerList) {
        for (ConfigChangeListener aListenerList : listenerList) {
            aListenerList.
                    configChanged(configChangeEvent);
        }
	}
    }

}