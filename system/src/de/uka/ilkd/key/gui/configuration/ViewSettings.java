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

package de.uka.ilkd.key.gui.configuration;

import java.util.LinkedList;
import java.util.Properties;

import de.uka.ilkd.key.gui.GUIEvent;

/**
 * This class encapsulates information about:
 * 1) relative font size in the prover view
 * 2) the maximal number of lines a tooltip with instantiated SchemaVariables
 *    is allowed to have. If this number is exceeded no SchemaVariables get
 *    instantiated in the displayed tooltip.
 * 3) wether intermediate proofsteps should be hidden in the proof tree view
 */
public class ViewSettings implements Settings, Cloneable {
    private static final String MAX_TOOLTIP_LINES_KEY = "[View]MaxTooltipLines";
    private static final String SHOW_WHOLE_TACLET = "[View]ShowWholeTaclet";
    private static final String FONT_INDEX = "[View]FontIndex";
    private static final String HIDE_INTERMEDIATE_PROOFSTEPS =
        "[View]HideIntermediateProofsteps";
    private static final String HIDE_AUTOMODE_PROOFSTEPS = "[View]HideAutomodeProofsteps";
    private static final String HIDE_CLOSED_SUBTREES =
        "[View]HideClosedSubtrees";
    private static final String USE_SYSTEM_LAF = "[View]UseSystemLookAndFeel";
    private static final String SHOW_JAVA_WARNING = "[View]ShowJavaWarning";
    private static final String PRETTY_SYNTAX = "[View]PrettySyntax";
    private static final String USE_UNICODE = "[View]UseUnicodeSymbols";
    private static final String CONFIRM_EXIT = "[View]ConfirmExit";

    /** default max number of displayed tooltip lines is 40 */
    private int maxTooltipLines = 40;
    /** do not print the find, varcond and heuristics part of taclets in
     * the TacletMenu by default */
    private boolean showWholeTaclet = false;
    /** default fontsize */
    private int sizeIndex = 2;
    /** do not hide intermediate proofsteps by default */
    private boolean hideIntermediateProofsteps = false;
    /** do not hide intermediate proofsteps by default */
    private boolean hideAutomodeProofsteps = false;
    /** do not hide closed subtrees by default */
    private boolean hideClosedSubtrees = false;
    /** whether to use system look and feel */
    private boolean useSystemLaF = false;
    private boolean notifyLoadBehaviour = true;
    /** Pretty Syntax is true by default, use Unicode symbols not */
    private boolean usePretty = true;
    private boolean useUnicode = false;
    /** confirm exiting by default */
    private boolean confirmExit = true;

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
     * Are system look and feel activated?
     */
    public boolean useSystemLaF(){
        return useSystemLaF;
    }

    /**
     * Sets the system look and feel option.
     */
    public void setUseSystemLaF(boolean b){
        if (b != useSystemLaF){
            useSystemLaF = b;
            fireSettingsChanged();
        }
    }

    /**
     * When loading a Java file, all other java files in the parent
     * directory are loaded as well.
     * Should there be a notification about this when opening a file?
     */
    public boolean getNotifyLoadBehaviour() {
    	return notifyLoadBehaviour;
    }

    /**
     * @param Whether a notification when opening a file should be shown
     */
    public void setNotifyLoadBehaviour(boolean show) {
    	notifyLoadBehaviour = show;
    }

    /**
     * @return true iff intermediate proof steps should be hidden
     */
    public boolean getHideIntermediateProofsteps() {
        return hideIntermediateProofsteps;
    }

    /**
     * @param hide Whether intermediate proof steps should be hidden
     */
    public void setHideIntermediateProofsteps(boolean hide) {
        if (hide != hideIntermediateProofsteps) {
            hideIntermediateProofsteps = hide;
            fireSettingsChanged();
        }
    }

    /**
     * @return true iff non-interactive proof steps should be hidden
     */
    public boolean getHideAutomodeProofsteps() {
        return hideAutomodeProofsteps;
    }

    /**
     * @param hide Whether non-interactive proof steps should be hidden
     */
    public void setHideAutomodeProofsteps(boolean hide) {
        if (hide != hideAutomodeProofsteps) {
            hideAutomodeProofsteps = hide;
            fireSettingsChanged();
        }
    }

    /**
     * @return true iff closed subtrees should be hidden
     */
    public boolean getHideClosedSubtrees() {
        return hideClosedSubtrees;
    }

    /**
     * @param hide Wether closed subtrees should be hidden
     */
    public void setHideClosedSubtrees(boolean hide) {
        if (hide != hideClosedSubtrees) {
            hideClosedSubtrees = hide;
            fireSettingsChanged();
        }
    }

    /** gets a Properties object and has to perform the necessary
     * steps in order to change this object in a way that it
     * represents the stored settings
     * @param props the collection of properties
     */
    public void readSettings(Object sender, Properties props) {
		String val1 = props.getProperty(MAX_TOOLTIP_LINES_KEY);
		String val2 = props.getProperty(FONT_INDEX);
		String val3 = props.getProperty(SHOW_WHOLE_TACLET);
		String val4 = props.getProperty(HIDE_INTERMEDIATE_PROOFSTEPS);
        String hideAuto = props.getProperty(HIDE_AUTOMODE_PROOFSTEPS);
		String val5 = props.getProperty(HIDE_CLOSED_SUBTREES);
		String val6 = props.getProperty(USE_SYSTEM_LAF);
		String val7 = props.getProperty(SHOW_JAVA_WARNING);
		String val8 = props.getProperty(PRETTY_SYNTAX);
		String val9 = props.getProperty(USE_UNICODE);
		String confirmExit = props.getProperty(CONFIRM_EXIT);
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
		if (hideAuto != null) {
		    hideAutomodeProofsteps = Boolean.valueOf(hideAuto);
		}
		if (val5 != null) {
			hideClosedSubtrees = Boolean.valueOf(val5)
				.booleanValue();
		}
		if (val6 != null) {
		    useSystemLaF = Boolean.valueOf(val6).booleanValue();
		}
		if (val7 != null) {
		    notifyLoadBehaviour = Boolean.valueOf(val7).booleanValue();
		}
		if (val8 != null) {
		    usePretty = Boolean.valueOf(val8).booleanValue();
		}
		if (val9 != null) {
		    useUnicode = Boolean.valueOf(val9).booleanValue();
		}
		if (confirmExit != null) {
		    this.confirmExit = Boolean.valueOf(confirmExit);
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
    public void writeSettings(Object sender,Properties props) {
    	props.setProperty(MAX_TOOLTIP_LINES_KEY, "" + maxTooltipLines);
    	props.setProperty(SHOW_WHOLE_TACLET, "" + showWholeTaclet);
    	props.setProperty(FONT_INDEX, "" + sizeIndex);
    	props.setProperty(HIDE_INTERMEDIATE_PROOFSTEPS, "" +
            hideIntermediateProofsteps);
        props.setProperty(HIDE_AUTOMODE_PROOFSTEPS, "" +
                hideAutomodeProofsteps);
    	props.setProperty(HIDE_CLOSED_SUBTREES, "" +
            hideClosedSubtrees);
    	props.setProperty(USE_SYSTEM_LAF, ""+useSystemLaF);
    	props.setProperty(SHOW_JAVA_WARNING, "" + notifyLoadBehaviour);
    	props.setProperty(PRETTY_SYNTAX, ""+ usePretty);
    	props.setProperty(USE_UNICODE, "" + useUnicode);
    	props.setProperty(CONFIRM_EXIT, ""+confirmExit);
    }

    /** sends the message that the state of this setting has been
     * changed to its registered listeners (not thread-safe)
     */
    protected void fireSettingsChanged() {
        for (SettingsListener aListenerList : listenerList) {
            aListenerList.settingsChanged(new GUIEvent(this));
        }
    }

    /**
     * adds a listener to the settings object
     * @param l the listener
     */
    public void addSettingsListener(SettingsListener l) {
	listenerList.add(l);
    }

public boolean isUsePretty() {
	return usePretty;
}

public void setUsePretty(boolean usePretty) {
	this.usePretty = usePretty;
	if(!usePretty){
	    setUseUnicode(false);
	}
	fireSettingsChanged();
}
/**
 * Use Unicode Symbols is only allowed if pretty syntax is used
 * @return setting of use unicode symbols (if use pretty syntax is on, return the value which is set, if use retty is false, return false)
 */
public boolean isUseUnicode() {
	if(isUsePretty()){
	return useUnicode;
	} else {
	setUseUnicode(false);
	return false;
	}

}

public void setUseUnicode(boolean useUnicode) {
	if(isUsePretty()){
	 this.useUnicode = useUnicode;
	} else {
	 this.useUnicode = false;
	}
	fireSettingsChanged();
}

    /** Whether to display the confirmation dialog upon exiting the main window. */
    public boolean confirmExit() {
        return confirmExit;
    }

    /** Set whether to display the confirmation dialog upon exiting the main window. */
    public void setConfirmExit(boolean confirmExit) {
        this.confirmExit = confirmExit;
        fireSettingsChanged();
    }

}
