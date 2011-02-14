// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

public class SVInstantiationParserException 
    extends SVInstantiationExceptionWithPosition {

    private String instantiation;
    private String detail;
         
    public SVInstantiationParserException( String  instantiation, 
					   int     row, 
					   int     column,
					   String  detail,
					   boolean inIfSequent) {
	super("Parser Error", row, column, inIfSequent);
	this.instantiation   = instantiation;
	this.detail = (detail == null) ? "" : detail;
    }
    
    private String space(int i) {
	StringBuffer res=new StringBuffer();
	for (int j=0; j<i; j++) {
	    res.append(" ");
	}
	return res.toString();
    }
    
    public String getMessage () {

	int column    = getColumn();	   

	String errmsg = super.getMessage();
	//needs non-prop font:	errmsg +="\n"+inst;
 	if (column > 0) {
	    //needs non-prop font: errmsg +="\n"+space(column-1)+"^";
	    StringBuffer sb = new StringBuffer( instantiation );
	    sb.insert(column-1, "~~>"+space(column-1));
	    errmsg +="\noccurred at: "+sb.toString();
 	} else {
	    errmsg += "\noccurred in:" + instantiation;
	}
	
	errmsg += "\nDetail:\n" + detail;
	
 	return errmsg;
    }    

    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
	return getMessage();
    }
}
