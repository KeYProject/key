// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.gui.assistant;

import java.io.IOException;
import java.net.URL;
import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.parser.dictionary.DictionaryLexer;
import de.uka.ilkd.key.parser.dictionary.DictionaryParser;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.KeYResourceManager;

/**
 * The dictionary of the proof assistant is encapsulated in this class
 * together with a simple parser. The dictionary is divided up into
 * sections which consists of key-value pairs. A new line means a new
 * key-value pair.
 */
class ProofAssistantDictionary {

    /** 
     * the dictionary  
     */
    private Map<String,String> dict = new HashMap<String,String>(20);


    public ProofAssistantDictionary() {
	parse(KeYResourceManager.getManager().
	      getResourceFile(this, "assistantDictionary.dct"));
    }

    /**
     * parse the directory file
     * @param dictFile the URL where the dictionary can be found
     */
    private void parse(URL dictFile) {
	try {
	    DictionaryParser parser = 
		new DictionaryParser(new DictionaryLexer(dictFile.openStream()));
	    parser.start();
	    dict = parser.getDictionary();
	} catch (IOException io) {
	    System.err.println("Failing loading dictionary for proof assistant.");
	    System.err.println("Proof assistant will not work.");
	    Debug.out("Thrown exception:", io);
	} catch (antlr.RecognitionException pe) {
	    System.err.println("Failing loading dictionary for proof assistant.");
	    System.err.println("Dictionary is corrupt.");
	    Debug.out("Thrown exception:", pe);
	} catch (antlr.TokenStreamException tse) {
	    System.err.println("Failing loading dictionary for proof assistant.");
	    System.err.println("Dictionary is corrupt.");
	    Debug.out("Thrown exception:", tse);
	}
    }

    /**
     * returns the stored text for the given key
     */
    public String get(String section, String key) {
	return dict.get(section+"."+key);
    }

}
