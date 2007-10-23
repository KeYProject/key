// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui.configuration;

import java.awt.Font;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import javax.swing.UIManager;




/** this class is used to set some default gui properties */
public class Config {

    public static final Config DEFAULT = new Config();

    /** name of different fonts */
    public static final String KEY_FONT_PROOF_TREE 
	= "KEY_FONT_PROOF_TREE";
    public static final String KEY_FONT_CURRENT_GOAL_VIEW 
	= "KEY_FONT_CURRENT_GOAL_VIEW";
    public static final String KEY_FONT_INNER_NODE_VIEW 
	= "KEY_FONT_INNER_NODE_VIEW";
    public static final String KEY_FONT_GOAL_LIST_VIEW 
	= "KEY_FONT_GOAL_LIST_VIEW";
    public static final String KEY_FONT_PROOF_LIST_VIEW 
	= "KEY_FONT_PROOF_LIST_VIEW";

    /** An array of font sizes for the goal view */
    private static final int[] sizes=new int[]{10,12,14,17,20,24};

    /** The index of the current size */
    private int sizeIndex = ProofSettings.DEFAULT_SETTINGS.getViewSettings().sizeIndex();

    /** cached ConfigChange event */
    private ConfigChangeEvent configChangeEvent = 
	new ConfigChangeEvent(this);

    /** the listeners to this Config */
    private List listenerList = new ArrayList(5);
    

    private Config() {
    }

    public void larger() {
	if (!isMaximumSize()) {
	    sizeIndex++;
	    ProofSettings.DEFAULT_SETTINGS.getViewSettings().setFontIndex(sizeIndex);
	    setDefaultFonts();
	    fireConfigChange(); 
	}
    }

    public void smaller() {
	if (!isMinimumSize()) {
	    sizeIndex--;
	    ProofSettings.DEFAULT_SETTINGS.getViewSettings().setFontIndex(sizeIndex);
	    setDefaultFonts(); 
	    fireConfigChange();
	}
    }

    public boolean isMinimumSize() {
	return sizeIndex==0;
    }
    
    public boolean isMaximumSize() {
	return sizeIndex==sizes.length-1;
    }

    public void setDefaultFonts() {
	UIManager.put(KEY_FONT_PROOF_TREE, 
		      new Font("Default", Font.PLAIN, sizes[sizeIndex]));
	UIManager.put(KEY_FONT_CURRENT_GOAL_VIEW, 
		      new Font("Monospaced", Font.PLAIN, sizes[sizeIndex]));
	UIManager.put(KEY_FONT_INNER_NODE_VIEW, 
		      new Font("Monospaced", Font.ITALIC, sizes[sizeIndex]));
	UIManager.put(KEY_FONT_GOAL_LIST_VIEW, 
		      new Font("Default", Font.PLAIN, sizes[2]));
	UIManager.put(KEY_FONT_PROOF_LIST_VIEW, 
		      new Font("Default", Font.PLAIN, sizes[2]));
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
	    Iterator it = listenerList.iterator();
	    while (it.hasNext()) {
		((ConfigChangeListener)it.next()).
		    configChanged(configChangeEvent);
	    }
	}
    }

}
