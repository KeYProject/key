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

package de.uka.ilkd.key.proof.io;

import java.io.File;
import java.util.List;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.speclang.PositionedString;


/** Represents the LDT .key files as a whole. Special treatment of these
 * files is necessary because their parts need to be read in a special
 * order, namely first all sort declarations then all function and predicate
 * declarations and third the rules. This procedure makes it possible to
 * use all declared sorts in all rules.
 */
public class LDTInput implements EnvInput {
    public interface LDTInputListener {
	public void reportStatus(String status, int progress);
    }

    private static final String NAME = "language data types";

    private final KeYFile[] keyFiles;
    private final LDTInputListener listener;
    private final Profile profile;

    private InitConfig initConfig = null;

    /** creates a representation of the LDT files to be used as input
     * to the KeY prover.
     * @param keyFiles an array containing the LDT .key files
     * @param main the main class used to report the progress of reading
     */
    public LDTInput(KeYFile[] keyFiles, LDTInputListener listener, Profile profile) {
   assert profile != null;
	this.keyFiles = keyFiles;
	this.listener=listener;
	this.profile = profile;
    }


    @Override
    public String name() {
	return NAME;
    }


    @Override
    public int getNumberOfChars() {
	int sum=0;
	for (int i=0; i<keyFiles.length; i++) {
	    sum=sum+keyFiles[i].getNumberOfChars();
	}
	return sum;
    }


    @Override
    public void setInitConfig(InitConfig conf) {
	this.initConfig=conf;
	for(int i = 0; i < keyFiles.length; i++) {
	    keyFiles[i].setInitConfig(conf);
	}
    }


    @Override
    public Includes readIncludes() throws ProofInputException {
	Includes result = new Includes();
	for(int i = 0; i < keyFiles.length; i++) {
	    result.putAll(keyFiles[i].readIncludes());
	}
	return result;
    }


    @Override
    public String readJavaPath() throws ProofInputException {
	return "";
    }


    // no class path elements here
    @Override
    public List<File> readClassPath() throws ProofInputException {
        return null;
    }


    // no class path elements here
    @Override
    public File readBootClassPath() {
        return null;
    }


    /** reads all LDTs, i.e., all associated .key files with respect to
     * the given modification strategy. Reading is done in a special order: first
     * all sort declarations then all function and predicate declarations and
     * third the rules. This procedure makes it possible to use all declared
     * sorts in all rules, e.g.
     */
    @Override
    public ImmutableSet<PositionedString> read() throws ProofInputException {
	if (initConfig==null) {
	    throw new IllegalStateException("LDTInput: InitConfig not set.");
	}

	for (int i=0; i<keyFiles.length; i++) {
	    keyFiles[i].readSorts();
	}
	for (int i=0; i<keyFiles.length; i++) {
	    keyFiles[i].readFuncAndPred();
	}
	for (int i=0; i<keyFiles.length; i++) {
	    if (listener != null) {
		listener.reportStatus("Reading " + keyFiles[i].name(),
				   keyFiles[i].getNumberOfChars());
	    }
	    keyFiles[i].readRules();
	}

        //create LDT objects
        initConfig.getServices().getTypeConverter().init();
        return DefaultImmutableSet.nil();
    }

    @Override
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


    @Override
    public int hashCode() {
	int result = 0;
	for(int i = 0; i < keyFiles.length; i++) {
	    result += keyFiles[i].hashCode();
	}
	return result;
    }

    @Override
    public String toString() {
	return name();
    }

    @Override
    public Profile getProfile() {
        return profile;
    }

    @Override
    public File getInitialFile() {
       return null;
    }
}
