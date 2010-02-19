// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.smt.test;

import java.io.File;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.Taclet;
import junit.framework.TestCase;

/**
 * Use this class for testing taclets: It provides a mechanism to load proofs
 * and taclet. Do not modify this class directly but derive subclasses to
 * implement tests.
 * 
 */

class TestTaclet extends TestCase {

    protected static String folder = System.getProperty("key.home")
	    + File.separator + "examples" + File.separator + "_testcase"
	    + File.separator + "smt" + File.separator + "tacletTranslation"
	    + File.separator;

    /** The set of taclets */
    private Collection<Taclet> taclets= new LinkedList<Taclet>();
    
    private Services services;
    
    protected Services getServices(){
	return services;
    }

    /**
     * Returns a set of taclets that can be used for tests. REMARK: First you
     * have to call <code>parse</code> to instantiate the set of taclets.
     * 
     * @return set of taclets.
     */
    protected Collection<Taclet> getTaclets() {
	if(taclets.isEmpty()){
	    parse();
	}
	return taclets;
    }
    
    protected HashSet<String> getTacletNames(){
	Collection<Taclet> set = getTaclets();
	HashSet<String> names = new HashSet<String>();
	for(Taclet taclet : set){
	    names.add(taclet.name().toString());
	}
	return names;
    }

    /**
     * Use this method if you only need taclets for testing.
     */
    protected ProofAggregate parse() {
	return parse(new File(folder + "dummyFile.key"));
    }

    /**
     * Calls
     * <code>parse(File file, Profile profile) with the standard profile for testing.
     */
    protected ProofAggregate parse(File file) {
	return parse(file, new JavaProfile());
    }

    /**
     * Parses a problem file and returns the corresponding ProofAggregate.
     * 
     * @param file
     *            problem file.
     * @profile determines the profile that should be used.
     * @return ProofAggregate of the problem file.
     */
    protected ProofAggregate parse(File file, Profile profile) {
	ProblemInitializer pi = null;
	ProofAggregate result = null;

	try {
	    KeYUserProblemFile po = new KeYUserProblemFile("test",
		    file, null);
	    
	    pi = new ProblemInitializer(profile);
	
	    
	    InitConfig initConfig = pi.prepare(po);
	    pi.startProver(initConfig, po);
	    
	    result = po.getPO();
	    services = initConfig.getServices();
	    taclets.clear();
	    for(Taclet t : initConfig.getTaclets() ){
		taclets.add(t);
	    }

	} catch (Exception e) {
	   assertTrue("Error while loading problem file "+ file+ ":\n\n" + e.getMessage(),false);
	}
	return result;
    }

}
