// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.unittest.cogent;

import de.uka.ilkd.key.logic.Term;

public class CogentResult{

    private boolean valid;
    private boolean error;
    private String counterEx="";

    public CogentResult(String res){
	valid = (res.indexOf("(valid)")!=-1 || res.indexOf("=")==-1);
	error = (res.indexOf("error")!=-1);
	if(!valid && !error){
	    if(res.indexOf("(not valid)")==-1){
		counterEx = res;
	    }else{
		counterEx = res.substring(res.indexOf("(not valid)")+12);
	    }
	}
    }

    public boolean valid(){
	return valid;
    }

    public boolean error(){
	return error;
    }

    public int getValueForTerm(Term t, CogentTranslation ct) 
	throws CogentException{
	String loc = ct.translate(t);
        String lineSeparator = System.getProperty("line.separator");
	int index = counterEx.indexOf(loc);
	if(index != -1){
	    index = counterEx.indexOf("=", index);
	    return Integer.parseInt(
		counterEx.substring(index+1, counterEx.indexOf(lineSeparator, 
							       index)));
	}else{
	    return 3;
	    //throw new CogentException("Term not found");
	}
    }
    
    public String toString(){
	return "CogentResult: valid="+valid+" error="+error+" counterEx="+counterEx;
    }

}
