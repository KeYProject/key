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

package de.uka.ilkd.key.smt.test;

import java.io.File;
import java.io.IOException;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

import junit.framework.Assert;
import junit.framework.TestCase;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.SMTTestSettings;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverType;

/**
 * Use this class for testing SMT: It provides a mechanism to load proofs and
 * taclets. Do not modify this class directly but derive subclasses to implement
 * tests.
 * 
 */
public abstract class TestCommons extends TestCase {
	private static HashMap<String, ProofAggregate> proofs = new HashMap<String, ProofAggregate>();
	protected static String folder = System.getProperty("key.home")
	        + File.separator + "examples" + File.separator + "_testcase"
	        + File.separator + "smt" + File.separator + "tacletTranslation"
	        + File.separator;
	/** The set of taclets */
	private Collection<Taclet> taclets = new LinkedList<Taclet>();
	InitConfig initConfig = null;
	static protected ProblemInitializer initializer = null;
	static protected Profile profile = init();

	static Profile init() {
		Profile p = new JavaProfile();
		return p;
	}

	private TermServices services;

	protected TermServices getServices() {
		return services;
	}

	/**
	 * returns the solver that should be tested.
	 * 
	 * @return the solver to be tested.
	 */
	public abstract SolverType getSolverType();

	public abstract boolean toolNotInstalled();

	protected boolean correctResult(String filepath, boolean isValid) {
		if (toolNotInstalled()) {
			return true;
		}
		SMTSolverResult result;
		try {
			result = checkFile(filepath);
		} catch (IOException e) {
			// must not happen!!
			System.out.println("Warning: " + this.getSolverType().getName()
			        + " produced error!!.");
			e.printStackTrace();
			// setToolNotInstalled(true);
			return true;
		}
		// System.gc();
		// unknown is always allowed. But wrong answers are not allowed
		return correctResult(isValid, result);
	}
	
	protected boolean correctResult(Goal g, boolean isValid){
		return correctResult(isValid, checkGoal(g));
	}

	private boolean correctResult(boolean isValid, SMTSolverResult result) {
		//System.out.println(Boolean.toString(isValid)+" "+result);
	    if (isValid && result != null) {
			return result.isValid() != SMTSolverResult.ThreeValuedTruth.FALSIFIABLE;
		} else {
			return result.isValid() != SMTSolverResult.ThreeValuedTruth.VALID;
		}
    }

	/**
	 * check a problem file
	 * 
	 * @param filepath
	 *            the path to the file
	 * @return the resulttype of the external solver
	 */
	protected SMTSolverResult checkFile(String filepath) throws IOException {
		ProofAggregate p = loadProof(filepath);
		Assert.assertTrue(p.getProofs().length == 1);
		Proof proof = p.getProofs()[0];
		Assert.assertTrue(proof.openGoals().size() == 1);
		Goal g = proof.openGoals().iterator().next();
		return checkGoal(g);
	}

	private SMTSolverResult checkGoal(Goal g) {
	    SolverLauncher launcher = new SolverLauncher(new SMTTestSettings());
		SMTProblem problem = new SMTProblem(g);
		launcher.launch(problem, g.proof().getServices(), getSolverType());
		return problem.getFinalResult();
    }
	
	

	protected ProofAggregate loadProof(String filepath) {
	    ProofAggregate p;
		if (!proofs.containsKey(filepath)) {
			File file = new File(filepath);
			p = parse(file);
			proofs.put(filepath, p);
		} else {
			p = proofs.get(filepath);
		}
	    return p;
    }

	/**
	 * Returns a set of taclets that can be used for tests. REMARK: First you
	 * have to call <code>parse</code> to instantiate the set of taclets.
	 * 
	 * @return set of taclets.
	 */
	protected Collection<Taclet> getTaclets() {
		if (taclets.isEmpty()) {
			if (initConfig == null) {
				parse();
			}
			for (Taclet t : initConfig.getTaclets()) {
				taclets.add(t);
			}
		}
		return taclets;
	}
	
	protected HashSet<String> getTacletNames() {
		Collection<Taclet> set = getTaclets();
		HashSet<String> names = new HashSet<String>();
		for (Taclet taclet : set) {
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
		return parse(file, profile);
	}

	/**
	 * Parses a problem file and returns the corresponding ProofAggregate.
	 * 
	 * @param file
	 *            problem file.
	 * @profile determines the profile that should be used.
	 * @return ProofAggregate of the problem file.
	 */
	protected ProofAggregate parse(File file, Profile pro) {
		ProofAggregate result = null;
		try {
			KeYUserProblemFile po = new KeYUserProblemFile(file.getName(),
			        file, null, pro);
			if (initializer == null) {
				initializer = new ProblemInitializer(po.getProfile());
			}
			initConfig = initializer.prepare(po);
			result = initializer.startProver(initConfig, po);
			services = initConfig.getServices();
			// po.close();
		} catch (Exception e) {
			assertTrue(
			        "Error while loading problem file " + file + ":\n\n"
			                + e.getMessage(), false);
		}
		return result;
	}
}

