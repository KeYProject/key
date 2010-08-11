// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

/* -*-antlr-*- */
header {

    package de.uka.ilkd.key.parser.dictionary;

    import java.io.*;
    import antlr.*;
    import java.util.Map;
    import java.util.HashMap;

}

/** 
 * Parser for dictionaries as e.g. required by the proof assistant
 */  
class DictionaryParser extends Parser;

options {
	importVocab=DictionaryLexer;
	k = 2;
}

{
	private Map<String,String> map = new HashMap<String,String>(20);

	public Map<String,String> getDictionary() {
	   return map;
	}

}


start :
	(
	  LBRACKET sectionId:IDENT RBRACKET
	  (keyId:IDENT EQUAL value:STRING_LITERAL 
		{
		   map.put(sectionId.getText()+"."+keyId.getText(),
			   value.getText());
		}
	  )*	
	)*
	;
