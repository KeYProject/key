// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.gui.configuration;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.Properties;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.gui.GUIEvent;

/** 
 * This class encapsulates information about:
 * 1) relative font size in the prover view
 * 2) the maximal number of lines a tooltip with instantiated SchemaVariables
 *    is allowed to have. If this number is exceeded no SchemaVariables get
 *    instantiated in the displayed tooltip.
 * 3) wether intermediate proofsteps should be hidden in the proof tree view
 */
public class ViewSettings implements Settings {
	static Logger logger = Logger.getLogger(ViewSettings.class.getName());
    private static final String MAX_TOOLTIP_LINES_KEY = "[View]MaxTooltipLines";
    private static final String SHOW_WHOLE_TACLET = "[View]ShowWholeTaclet";
    private static final String FONT_INDEX = "[View]FontIndex";
    private static final String HIDE_INTERMEDIATE_PROOFSTEPS =
        "[View]HideIntermediateProofsteps";


    /** default max number of displayed tooltip lines is 40 */
    private int maxTooltipLines = 40; 
    /** do not print the find, varcond and heuristics part of taclets in
     * the TacletMenu by default */
    private boolean showWholeTaclet = false;
    /** default fontsize */
    private int sizeIndex = 2;
    /** do not hide intermediate proofsteps by default */
    private boolean hideIntermediateProofsteps = false;


    private LinkedList<SettingsListener> listenerList =
        new LinkedList<SettingsListener>();


    /**
     * @return the current maxTooltipLines
     */
    public int getMaxTooltipLines() {
    	return maxTooltipLines;
    }

    /**
     * Sets maxTooltipLines 
     * @param b The new value for maxTooltipLines 
     */
    public void setMaxTooltipLines(int b) {
          if(b != maxTooltipLines) {
		maxTooltipLines = b;
		fireSettingsChanged();
	  }
    }
    
    /**
     * returns whether the Find and VarCond part of Taclets should be
     * pretty-printed with instantiations of schema-variables or not
     * 
     * @return true iff the find part should be pretty-printed instantiated
     */
    public boolean getShowWholeTaclet() {
        return showWholeTaclet;
    }

    /**
     * Sets whether the Find and VarCond part of Taclets should be
     * pretty-printed with instantiations of schema-variables or not
     * 
     * @param b
     *           indicates whether the Find and VarCond part of Taclets should
     *           be pretty-printed with instantiations of schema-variables or
     *           not
     */
    public void setShowWholeTaclet(boolean b) {
        if(b != showWholeTaclet) {
            showWholeTaclet = b;
            fireSettingsChanged();
        }
    }

    /**
     * @return the current sizeIndex
     */
    public int sizeIndex() {
    	return sizeIndex;
    }

     /**
     * Sets FontIndex
     * @param b The new value for SizeIndex 
     */
    public void setFontIndex(int b) {
        if(b != sizeIndex) {
            sizeIndex = b;
            fireSettingsChanged();
        }
    }

    /**
     * @return true iff intermediate proofsteps should be hidden
     */
    public boolean getHideIntermediateProofsteps() {
        return hideIntermediateProofsteps;
    }

    /**
     * @param hide Wether intermediate proofsteps should be hidden
     */
    public void setHideIntermediateProofsteps(boolean hide) {
        if (hide != hideIntermediateProofsteps) {
            hideIntermediateProofsteps = hide;
            fireSettingsChanged();
        }
    }

    /** gets a Properties object and has to perform the necessary
     * steps in order to change this object in a way that it
     * represents the stored settings
     * @param props the collection of properties  
     */
    public void readSettings(Properties props) {
		String val1 = props.getProperty(MAX_TOOLTIP_LINES_KEY);
		String val2 = props.getProperty(FONT_INDEX);
		String val3 = props.getProperty(SHOW_WHOLE_TACLET);
		String val4 = props.getProperty(HIDE_INTERMEDIATE_PROOFSTEPS);
		if (val1 != null) {
		        maxTooltipLines = Integer.valueOf(val1).intValue();
		} 
		if (val2 != null) {
			sizeIndex = Integer.valueOf(val2).intValue();
		}
		if (val3 != null) {
			showWholeTaclet = Boolean.valueOf(val3).booleanValue();
		}
		if (val4 != null) {
			hideIntermediateProofsteps = Boolean.valueOf(val4)
				.booleanValue();
		}
	}

  
    /**
	 * implements the method required by the Settings interface. The settings
	 * are written to the given Properties object. Only entries of the form
	 * <key>=<value>(, <value>)* are allowed.
	 * 
	 * @param props
	 *           the Properties object where to write the settings as (key,
	 *           value) pair
	 */
    public void writeSettings(Properties props) {
    	props.setProperty(MAX_TOOLTIP_LINES_KEY, "" + maxTooltipLines);
    	props.setProperty(SHOW_WHOLE_TACLET, "" + showWholeTaclet);
    	props.setProperty(FONT_INDEX, "" + sizeIndex);
    	props.setProperty(HIDE_INTERMEDIATE_PROOFSTEPS, "" +
            hideIntermediateProofsteps);
    }

    /** sends the message that the state of this setting has been
     * changed to its registered listeners (not thread-safe)
     */
    protected void fireSettingsChanged() {
	Iterator<SettingsListener> it = listenerList.iterator();
	while (it.hasNext()) {
	    it.next().settingsChanged(new GUIEvent(this));
	}
    }

    /** 
     * adds a listener to the settings object 
     * @param l the listener
     */
    public void addSettingsListener(SettingsListener l) {
	listenerList.add(l);
    }
    
}
