// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.casetool.ModelMethod;

public class ContractUtil {

    private ContractUtil() {}

    public static PrePostPair getPreInvPost(ModelMethod m) {
	String pre = "(" + normalizeConstraint(m.getMyPreCond()) 
	    + ")" + " and " +  "(" 
	    + normalizeConstraint(m.getContainingClass().getMyInv()) + ")";
	String post = normalizeConstraint(m.getMyPostCond());
	return new PrePostPair(pre, post);
    }

    public static PrePostPair getPrePost(ModelMethod m) {
	String pre = "(" + normalizeConstraint(m.getMyPreCond()) 
	    + ")";
	String post = normalizeConstraint(m.getMyPostCond());
	pre=pre.trim();
	post=post.trim();
	return new PrePostPair(pre, post);
    }

    public static PrePostPair getPreInvPostInv(ModelMethod m) {
	String inv = normalizeConstraint(m.getContainingClass().getMyInv());
	String pre = "(" + normalizeConstraint(m.getMyPreCond()) 
	    + ")" + " and " +  "(" 
	    + inv + ")";
	String post = "(" + normalizeConstraint(m.getMyPostCond()) +")" 
	    + " and " + "(" + inv + ")";
	return new PrePostPair(pre, post);
    }

    public static PrePostPair getPreInvInv(ModelMethod m) {
	String inv = normalizeConstraint(m.getContainingClass().getMyInv());
	String pre = "(" + normalizeConstraint(m.getMyPreCond()) 
	    + ")" + " and " +  "(" 
	    + inv + ")";
	return new PrePostPair(pre, inv);
    }

    public static PrePostPair getPreInvTout(ModelMethod m) {
	String poToutText;
	if (m.getContainingClassName().equals(m.getName())){
	    poToutText="";
	} else {
	    poToutText= "("+normalizeConstraint(m.getMyPreCond())+")" 
                + " and " + "(" 
		+ normalizeConstraint(m.getContainingClass().getMyInv()) + ")" 
		+ " and " + "("
		+normalizeConstraint
		(m.getContainingClass().getMyThroughout())+")";
	}
	return new PrePostPair
	    (poToutText, normalizeConstraint
	     (m.getContainingClass().getMyThroughout()));
    }


    /**
     * Converts an empty string to "true" and keeps it unchanged otherwise.
     */
    public static String normalizeConstraint(String aText) {
        if (aText.equals("")){
            return "true";
        } else {
            return aText;
        }
    }
    
  

}
