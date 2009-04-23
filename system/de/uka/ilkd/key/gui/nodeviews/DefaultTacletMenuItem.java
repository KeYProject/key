// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.gui.nodeviews;

import java.io.StringWriter;
import java.io.Writer;

import javax.swing.JMenuItem;

import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.pp.WriterBackend;

/** 
 * this class extends JMenuItem. The objective is to store
 * the Taclet of each item in the item for easier access to the Taclet
 * if the item has been selected 
 */
class DefaultTacletMenuItem extends JMenuItem implements TacletMenuItem {
    
    private TacletApp connectedTo;
    
    /** creates TacletMenuItem attached to a Taclet 
     * @param connectedTo the TacletApp that is represented by the item 
     * @param notationInfo the NotationInfo used to print terms
     */
    public DefaultTacletMenuItem(JMenuItem menu, 
            TacletApp connectedTo, NotationInfo notationInfo) {
        super(connectedTo.taclet().displayName());
        this.connectedTo = connectedTo;	    	    
        StringBuffer taclet_sb = new StringBuffer();
        Writer w = new StringWriter();
        
        WriterBackend backend = new WriterBackend(w, 68);
        LogicPrinter tp = new LogicPrinter(new ProgramPrinter(w,
    							  connectedTo.instantiations()),
    				       notationInfo, backend, null,
    				       true);
        tp.printTaclet(connectedTo.taclet(), connectedTo.instantiations(),
    		   ProofSettings.DEFAULT_SETTINGS.getViewSettings()
    		   .getShowWholeTaclet());
        
        int nlcount = 0;
        StringBuffer sb = new StringBuffer(w.toString());
        int sbl = sb.length();
        for (int i = 0; i < sbl; i++) {
    	if (sb.charAt(i) == '\n') {
    	    nlcount += 1;
    	}
        }
        if (nlcount > ProofSettings.DEFAULT_SETTINGS.getViewSettings().getMaxTooltipLines()) { 
    	if (TacletMenu.logger.isDebugEnabled()) {
    	    TacletMenu.logger.debug("No SchemaVariable instantiation printed, linecount is " 
    			 + nlcount + " > " 
    			 + ProofSettings.DEFAULT_SETTINGS.
    			 getViewSettings().getMaxTooltipLines());
    	}
    	taclet_sb = new StringBuffer();
    	w = new StringWriter();
    	backend = new WriterBackend(w, 68);
    	tp = new LogicPrinter
    	    (new ProgramPrinter(w), notationInfo, backend, null, true);
    	tp.printTaclet(connectedTo.taclet());

        }

        taclet_sb.append(ascii2html(new StringBuffer(w.toString())));
        taclet_sb.replace(0,0,"<html><pre>");
        taclet_sb.append("</pre>");


        setToolTipText(taclet_sb.toString());
    } 
    
    /**
     * Replaces <,>,& and new lines with their HTML masks.
     * @param sb The StringBuffer with forbidden HTML characters
     * @return A new StringBuffer with the masked characters.
     */
    protected StringBuffer ascii2html(StringBuffer sb) {
        StringBuffer nsb = new StringBuffer();
        StringBuffer asb = removeEmptyLines(sb);
        int sbl = asb.length();
        for (int i = 0; i < sbl; i++) {
        	switch (asb.charAt(i)) {
    	case '<'	: nsb.append("&lt;"); break;
    	case '>'	: nsb.append("&gt;"); break;
    	case '&'	: nsb.append("&amp;"); break;
    	case '\n'	: nsb.append("<br>"); break;
    	default		: nsb.append(asb.charAt(i));
        	}
        }
        return nsb;
    }

    protected StringBuffer removeEmptyLines(StringBuffer sb) {
        String s = sb.toString();
        String[] sa = s.split("\n");
        StringBuffer result = new StringBuffer();
        for (int i = 0; i < sa.length; i ++) {
    	//logger.debug("'" + sa[i] + "'");
    	if (sa[i] == "") {
    	    continue;
    	}
    	boolean onlySpaces = true;
    	for (int j = 0; j < sa[i].length(); j++) {
    	    if (sa[i].charAt(j) != ' ') {
    		onlySpaces = false;
    	    }
    	}
    	if (onlySpaces) {
    	    continue;
    	}
    	result.append(sa[i]).append("\n");
        }
        if (result.charAt(result.length()-1) == '\n') {
    	result.setLength(result.length() - 1);
        }
        return result;
    }
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.gui.TacletMenuItem#connectedTo()
     */
    public TacletApp connectedTo() {
        return connectedTo;
    }

}
