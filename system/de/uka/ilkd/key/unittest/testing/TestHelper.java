// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.unittest.testing;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.*;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.ProblemLoader;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.JavaTestGenerationProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.unittest.UnitTestBuilder;

/**
 * This class "wraps" a proof in KeY. It is needed only for the KeY junittests,
 * namely the class TestTestGenerator
 * 
 * @author mbender
 */
public class TestHelper {

    public static final String ABS_MIN_NAME = "AbsMin";

    public static final String BRANCHING_LOOP_NAME = "BrachingLoop";

    private final String name;

    private final String file;

    private final SimpleStarter main;

    private final KeYMediator medi;

    private final Proof proof;

    private final UnitTestBuilder utb;

    private final DataStorage data;

    private final ImmutableSet<ProgramMethod> pms;

    private ArrayList<HashMap<String, Expression>> combLocDat = null;

    final Object semaphorLoad = new Object();

    final Object semaphorProof = new Object();

    final static String PATH = System.getProperty("key.home") + File.separator
	    + "examples" + File.separator + "_testcase" + File.separator
	    + "testgen" + File.separator;

    public TestHelper(final String file, final String name, final boolean prove) {
	// Init
	this.file = PATH + file;
	this.name = name;
	main = new SimpleStarter(this.file, createPTListener());
	medi = new KeYMediator(main);
	main.setKeYMediator(medi);
	// Loading
	medi.addAutoModeListener(createAMListener());
	final Profile profil = (prove ? new JavaTestGenerationProfile(main)
	        : new JavaProfile(main));
	ProofSettings.DEFAULT_SETTINGS.setProfile(profil);
	synchronized (semaphorLoad) {
	    try {
		main.loadCommandLineFile();
		semaphorLoad.wait();
	    } catch (final InterruptedException e1) {
		e1.printStackTrace();
	    }
	}
	proof = medi.getProof();
	// Proving
	if (prove) {
	    medi.setSimplifier(ProofSettings.DEFAULT_SETTINGS
		    .getSimultaneousUpdateSimplifierSettings().getSimplifier());
	    medi.setMaxAutomaticSteps(1000);
	    medi.getProof().setActiveStrategy(
		    profil.getDefaultStrategyFactory().create(proof, null));
	    synchronized (semaphorProof) {
		try {
		    medi.startAutoMode();
		    semaphorProof.wait();
		} catch (final InterruptedException e1) {
		    e1.printStackTrace();
		}
	    }
	}
	// Testing
	utb = new UnitTestBuilder(medi.getServices(), proof, true);
	utb.createTestForProof(proof);
	data = utb.getDS();
	pms = data.getPms();
    }

    public Proof getProof() {
	return proof;
    }

    public int getNrofOG() {
	return proof.openEnabledGoals().size();
    }

    public String getFName() {
	return file;
    }

    public int nrOfMeth() {
	return pms.size();
    }

    public String methNames() {
	String result = "";
	final Iterator<ProgramMethod> iter = pms.iterator();
	while (iter.hasNext()) {
	    result = result.concat(iter.next().toString());
	}
	return result;
    }

    public int getNrOfNodes() {
	return data.getNodeCount();
    }

    public int getNrOfStatements() {
	return data.getCode().length;
    }

    public int getNrOfMGS() {
	return data.getNrOfMgs();
    }

    public int getNrOfPV() {
	return data.getPvs().size();
    }

    public boolean isOracleNnull() {
	return data.getOracle() != null;
    }

    public int getNrOfPV2() {
	return data.getPvs2().size();
    }

    public int getNrOfTestDat() {
	return data.getNrOfTestDat();
    }

    private ArrayList<HashMap<String, Expression>> combLocDat() {
	if (combLocDat == null) {
	    final ArrayList<Expression[][]> locs = data.getTestLoc();
	    final ArrayList<Expression[][]> dats = data.getTestDat();
	    assert locs.size() == dats.size();
	    final ArrayList<HashMap<String, Expression>> result = new ArrayList<HashMap<String, Expression>>();
	    HashMap<String, Expression> tmp;
	    for (int i = 0; i < locs.size(); i++) {
		tmp = new HashMap<String, Expression>();
		if (locs.get(i) != null) {
		    for (int j = 0; j < locs.get(i).length; j++) {
			if (locs.get(i)[j] != null) {
			    tmp.put(((LocationVariable) locs.get(i)[j][0])
				    .name().toString(), dats.get(i)[j][0]);
			    // System.out.println(" " + i + " " + j + " " + " "
			    // + locs.get(i)[j][0] + " := "
			    // + dats.get(i)[j][0]);
			}
		    }
		    if (tmp.size() != 0) {
			result.add(tmp);
		    }
		}
	    }
	    combLocDat = result;
	}
	return combLocDat;

    }

    public boolean checkTestData() {
	if (name.equals(ABS_MIN_NAME)) {
	    return checkAbsMinTD();
	} else if (name.equals(BRANCHING_LOOP_NAME)) {
	    return checkBrLoopTD();
	} else {
	    return false;
	}
    }

    private boolean checkAbsMinTD() {
	final ArrayList<HashMap<String, Expression>> cData = combLocDat();
	boolean case1 = false;
	boolean case2 = false;
	boolean case3 = false;
	boolean case4 = false;
	int a;
	int b;

	for (final HashMap<String, Expression> map : cData) {
	    a = Integer.parseInt(map.get("a").toString());
	    b = Integer.parseInt(map.get("b").toString());
	    if (a == 0) {
		if (b == 0) {
		    case1 = true;
		} else if (b > 0) {
		    case2 = true;
		}
	    } else if (a < 0) {
		if (b == 0) {
		    case3 = true;
		} else if (b < 0) {
		    case4 = true;
		}
	    }
	}
	return case1 && case2 && case3 && case4;
    }

    private boolean checkBrLoopTD() {
	int n0;
	int n1;
	Expression n0e;
	Expression n1e;
	for (final HashMap<String, Expression> map : combLocDat()) {
	    n0e = map.get("_n_0");
	    n1e = map.get("_n_1");
	    if (n0e != null) {
		n0 = Integer.parseInt(n0e.toString());
		if (n0 > 20) {
		    return true;
		}
	    }
	    if (n1e != null) {
		n1 = Integer.parseInt(n1e.toString());
		n1 = Integer.parseInt(n1e.toString());
		if (n1 > 20) {
		    return true;
		}
	    }
	}
	return false;
    }

    public String wrongData() {
	if (name.equals(ABS_MIN_NAME)) {
	    return AbsMinWrongData();
	} else if (name.equals(BRANCHING_LOOP_NAME)) {
	    return BrLoopWrongData();
	} else {
	    return "";
	}
    }

    private String AbsMinWrongData() {
	String result = "\nThe test data to test absMin is wrong.\nFollowing cases need to be covered"
	        + "\n a==0 && b==0"
	        + "\n a==0 && b>0"
	        + "\n a<0 && b==0"
	        + "\n a<0 && b<0" + "\nThe generated test data is as follows:";
	int a;
	int b;
	for (final HashMap<String, Expression> map : combLocDat()) {
	    a = Integer.parseInt(map.get("a").toString());
	    b = Integer.parseInt(map.get("b").toString());
	    result = result.concat("\na= " + a + "   b= " + b);

	}
	return result;
    }

    private String BrLoopWrongData() {
	final String result = "\nThe test data to test BranchingLoop is wrong.\nThere must be at least one case where n is larger than 20"
	        + "\nThe generated test data is as follows:\n" + combLocDat();
	return result;
    }

    private ProverTaskListener createPTListener() {
	return new ProverTaskListener() {

	    public void taskStarted(final String message, final int size) {
	    }

	    public void taskProgress(final int position) {
	    }

	    public void taskFinished(final TaskFinishedInfo info) {
		if (info.getSource() instanceof ProblemLoader) {
		    synchronized (semaphorLoad) {
			semaphorLoad.notifyAll();
		    }
		}

	    }
	};
    }

    private AutoModeListener createAMListener() {
	return new AutoModeListener() {

	    public void autoModeStopped(final ProofEvent e) {
		if (e.getSource() != null) {
		    synchronized (semaphorProof) {
			semaphorProof.notifyAll();
		    }
		}
	    }

	    public void autoModeStarted(final ProofEvent e) {
	    }
	};
    }

}
