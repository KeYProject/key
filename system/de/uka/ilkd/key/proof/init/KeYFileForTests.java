// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.proof.init;

import java.io.File;
import java.io.FileNotFoundException;

import de.uka.ilkd.key.parser.KeYLexer;
import de.uka.ilkd.key.parser.KeYParser;
import de.uka.ilkd.key.parser.ParserConfig;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.proof.CountingBufferedInputStream;
import de.uka.ilkd.key.proof.RuleSource;

/**
 * Used for TESTS ONLY as we allow there to declare program variables global 
 * in rule files .
 */
public class KeYFileForTests extends KeYFile {

    /** creates a new representation for a given file by indicating a name
     * and a file representing the physical source of the .key file.
     */
    public KeYFileForTests(String name, File file) {
	super(name, file, null, false);
    }

    /** reads the whole .key file and modifies the initial configuration
     * assigned to this object according to the given modification strategy. 
     * Throws an exception if no initial configuration has been set yet.
     */
    public void read(ModStrategy mod) throws ProofInputException {
	if (initConfig==null) {
	    throw new IllegalStateException("KeYFile: InitConfig not set.");
	}
	try {
	    final CountingBufferedInputStream cinp = 
		new CountingBufferedInputStream
		    (getNewStream(),monitor,getNumberOfChars()/100);
	    final ParserConfig pc = 
		new ParserConfig(initConfig.getServices().copy(), 
				 initConfig.namespaces().copy());
	    KeYParser problemParser = new KeYParser
		(ParserMode.PROBLEM,new KeYLexer(cinp,null), file.toString(), pc, pc,initConfig.
		 getTaclet2Builder(), initConfig.getTaclets(),initConfig.getActivatedChoices()); 
            problemParser.problem(); 
	    initConfig.setTaclets(problemParser.getTaclets()); 
	    initConfig.add(problemParser.namespaces(), ModStrategy.MOD_ALL);
	} catch (antlr.ANTLRException e) {
	    throw new ProofInputException(e);
	} catch (FileNotFoundException ioe) {
            throw new ProofInputException(ioe);
        }
    }
    
    public Includes readIncludes() throws ProofInputException {
	Includes result = super.readIncludes();
        		      
	//add test LDTs
        if(result.getLDTIncludes().isEmpty()) {
            result.put("ldtsForTests", 
        	       RuleSource.initRuleFile("LDTsForTestsOnly.key"));
        }
        
        return result;
    }
}
