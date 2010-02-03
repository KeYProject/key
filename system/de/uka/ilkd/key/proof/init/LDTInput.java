// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.proof.init;

import java.util.List;
import java.io.File;

import de.uka.ilkd.key.gui.IMain;
import de.uka.ilkd.key.gui.configuration.LibrariesSettings;
import de.uka.ilkd.key.java.recoderext.RecoderModelTransformer;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.IteratorOfNamed;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.ldt.BooleanLDT;
import de.uka.ilkd.key.logic.ldt.ByteLDT;
import de.uka.ilkd.key.logic.ldt.CharLDT;
import de.uka.ilkd.key.logic.ldt.IntLDT;
import de.uka.ilkd.key.logic.ldt.IntegerDomainLDT;
import de.uka.ilkd.key.logic.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.ldt.ListOfLDT;
import de.uka.ilkd.key.logic.ldt.LongLDT;
import de.uka.ilkd.key.logic.ldt.SLListOfLDT;
import de.uka.ilkd.key.logic.ldt.ShortLDT;


/** Represents the LDT .key files as a whole. Special treatment of these
 * files is necessary because their parts need to be read in a special 
 * order, namely first all sort declarations then all function and predicate 
 * declarations and third the rules. This procedure makes it possible to 
 * use all declared sorts in all rules.
 */
public class LDTInput implements EnvInput {
    private static final String NAME = "language data types";
    
    private final KeYFile[] keyFiles;
    private final IMain main;
    
    private InitConfig initConfig = null;


    /** creates a representation of the LDT files to be used as input
     * to the KeY prover.  
     * @param keyFiles an array containing the LDT .key files
     * @param main the main class used to report the progress of reading
     */
    public LDTInput(KeYFile[] keyFiles, IMain main) {
	this.keyFiles = keyFiles;
	this.main=main;
    }
    
    
    public String name() {
	return NAME;
    }
    
    
    public RecoderModelTransformer getTransformer() {
        return null;
    }
    
    
    public int getNumberOfChars() {
	int sum=0;
	for (int i=0; i<keyFiles.length; i++) {
	    sum=sum+keyFiles[i].getNumberOfChars();
	}
	return sum;
    }


    public void setInitConfig(InitConfig conf) {
	this.initConfig=conf;	
	for(int i = 0; i < keyFiles.length; i++) {
	    keyFiles[i].setInitConfig(conf);
	}
    }

    
    public Includes readIncludes() throws ProofInputException {
	Includes result = new Includes();
	for(int i = 0; i < keyFiles.length; i++) {
	    result.putAll(keyFiles[i].readIncludes());
	}
	return result;
    }
    
    
    public LibrariesSettings readLibrariesSettings() 
    		throws ProofInputException {
	return new LibrariesSettings();
    }
    
    
    public String readJavaPath() throws ProofInputException {
	return "";
    }
    public List<File> readClassPath() throws ProofInputException {
        return null;
    }

    
    /** reads all LDTs, i.e., all associated .key files with respect to 
     * the given modification strategy. Reading is done in a special order: first
     * all sort declarations then all function and predicate declarations and
     * third the rules. This procedure makes it possible to use all declared
     * sorts in all rules, e.g.
     */
    public void read(ModStrategy mod) throws ProofInputException {
	if (initConfig==null) {
	    throw new IllegalStateException("LDTInput: InitConfig not set.");
	}
	for (int i=0; i<keyFiles.length; i++) {
	    keyFiles[i].readSorts(mod);
	}
	for (int i=0; i<keyFiles.length; i++) {
	    keyFiles[i].readFuncAndPred(mod);
	}
	for (int i=0; i<keyFiles.length; i++) {
	    if (main != null) {
		main.setStatusLine("Reading "+keyFiles[i].name(), 
				   keyFiles[i].getNumberOfChars());
	    }
	    keyFiles[i].readRulesAndProblem(mod);
	}
	
	//create LDTs
        Namespace sorts     = initConfig.sortNS();
        Namespace functions = new Namespace(initConfig.funcNS());
        IteratorOfNamed it = initConfig.choiceNS().allElements().iterator();
        while(it.hasNext()) {
            Choice c = (Choice) it.next();
            functions.add(c.funcNS());
        }
        ListOfLDT ldts = SLListOfLDT.EMPTY_LIST
                        	.prepend(new ByteLDT(sorts, functions))
                        	.prepend(new ShortLDT(sorts, functions))
                        	.prepend(new IntLDT(sorts, functions))
                        	.prepend(new LongLDT(sorts, functions))
                        	.prepend(new CharLDT(sorts, functions))
                        	.prepend(new IntegerLDT(sorts, functions))
                        	.prepend(new IntegerDomainLDT(sorts, functions))
                        	.prepend(new BooleanLDT(sorts, functions));
        initConfig.getServices().getTypeConverter().init(ldts);
    }
  
    
    public boolean equals(Object o){
	if(!(o instanceof LDTInput)) {
	    return false;
	}
	
	LDTInput li = (LDTInput) o;
	if(keyFiles.length != li.keyFiles.length){
	    return false;
	}
	
        for(int i = 0; i < keyFiles.length; i++) {
            boolean found = false;
            for(int j = 0; j < keyFiles.length; j++) {
        	if(li.keyFiles[j].equals(keyFiles[i])) {
        	    found = true;
        	    break;
        	}
            }
            if(!found) {
        	return false;
            }
        }
	
	return true;
    }
    
    
    public int hashCode() {
	int result = 0;
	for(int i = 0; i < keyFiles.length; i++) {
	    result += keyFiles[i].hashCode();
	}
	return result;
    }



}
