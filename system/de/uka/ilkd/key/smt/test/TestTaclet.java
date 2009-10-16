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

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.proof.ProofAggregate;
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
	    + File.separator + "smt" + File.separator + "TacletTranslation"
	    + File.separator;

    /** The set of taclets */
    private ImmutableSet<Taclet> taclets;

    /**
     * Returns a set of taclets that can be used for tests. REMARK: First you
     * have to call <code>parse</code> to instantiate the set of taclets.
     * 
     * @return set of taclets.
     */
    protected ImmutableSet<Taclet> getTaclets() {
	return taclets;
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
	    KeYUserProblemFile po = new KeYUserProblemFile("UpdatetermTest",
		    file, null);
	    pi = new ProblemInitializer(profile);
	    pi.startProver(po, po);

	    result = po.getPO();
	    taclets = pi.prepare(po).getTaclets();

	} catch (Exception e) {
	    System.err.println("Exception occurred while parsing " + file
		    + "\n");
	    e.printStackTrace();
	    System.exit(-1);
	}
	return result;
    }

}
