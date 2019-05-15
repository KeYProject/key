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

package de.uka.ilkd.key.smt.lang;

public class Util {
	public static String processName(String id){
		//is symbol already quoted?
		if(id.startsWith("|") && id.endsWith("|")){
			return id;
		}


		//id = id.replace("store", "store_");
		id = id.replace("select", "select_");


		//do i need to quote symbol?
		boolean quote = id.contains(":") ||
				id.contains(">") ||
				id.contains("<") ||
				id.contains("$") ||		
				id.contains("[") ||
				id.contains("]") ;

		if(quote){
			return "|"+id+"|";
		}
		else{
			return id;
		}
	}
}