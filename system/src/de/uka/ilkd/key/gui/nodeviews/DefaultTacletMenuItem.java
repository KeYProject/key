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


package de.uka.ilkd.key.gui.nodeviews;

import java.io.StringWriter;
import java.io.Writer;

import javax.swing.JMenuItem;

import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.pp.WriterBackend;

/** 
 * this class extends JMenuItem. The objective is to store
 * the Taclet of each item in the item for easier access to the Taclet
 * if the item has been selected 
 */
class DefaultTacletMenuItem extends JMenuItem implements TacletMenuItem {
    
    /**
     * 
     */
    private static final long serialVersionUID = -5537139155045230424L;
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
        StringWriter w = new StringWriter();
        
        WriterBackend backend = new WriterBackend(w, 68);
        LogicPrinter tp = new LogicPrinter(new ProgramPrinter(w,
    							  connectedTo.instantiations()),
    				       notationInfo, backend, null,
    				       true);
        tp.printTaclet(connectedTo.taclet(), 
        	       connectedTo.instantiations(),
        	       ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getShowWholeTaclet(),
//        	       ProofSettings.DEFAULT_SETTINGS.getViewSettings().getShowWholeTaclet(),
        	       false);
        
        int nlcount = 0;

        StringBuffer sb = w.getBuffer();
        int maxTooltipLines = ProofIndependentSettings.DEFAULT_INSTANCE.
                getViewSettings().getMaxTooltipLines();
        
        // replaced the old code here to fix #1340. (MU)
        int sbl = sb.length();
        boolean truncated = false;
        for (int i = 0; i < sbl && !truncated; i++) {
            if (sb.charAt(i) == '\n') {
        	nlcount += 1;
        	if(nlcount > maxTooltipLines){
        	    sb.setLength(i);
        	    truncated = true;
        	}
            }
        }

        taclet_sb.append("<html><pre>");
        taclet_sb.append(ascii2html(sb));
        taclet_sb.append("</pre>");
        if(truncated) {
            taclet_sb.append("\n<b>!!</b><i> Message has been truncated. " +
                    "See View &rarr; ToolTip Options.</i>");
        }

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
        for (String aSa : sa) {
            //logger.debug("'" + sa[i] + "'");
            if ("".equals(aSa)) {
                continue;
            }
            boolean onlySpaces = true;
            for (int j = 0; j < aSa.length(); j++) {
                if (aSa.charAt(j) != ' ') {
                    onlySpaces = false;
                }
            }
            if (onlySpaces) {
                continue;
            }
            result.append(aSa).append("\n");
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
