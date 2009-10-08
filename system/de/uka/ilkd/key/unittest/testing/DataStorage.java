// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest.testing;

import java.util.ArrayList;
import java.util.LinkedList;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.unittest.ModelGenerator;
import de.uka.ilkd.key.unittest.TestGenerator;
import de.uka.ilkd.key.visualization.ExecutionTraceModel;

/**
 * This class stores certain values during the test case generation of KeY. It
 * is needed only for the KeY junittests, namely the classes TestHelper and
 * UniTestBuilder
 * 
 * @author mbender
 * 
 */
public class DataStorage {

    private ImmutableSet<ProgramMethod> pms;

    private final LinkedList<ExecutionTraceModel[]> allETM = new LinkedList<ExecutionTraceModel[]>();

    private int nodeCount;

    private Statement[] code;

    private Term oracle;

    private LinkedList<ModelGenerator> mgs;

    private ImmutableSet<ProgramVariable> pvs;

    private TestGenerator tg;

    private ImmutableSet<ProgramVariable> pvs2;

    private final ArrayList<Expression[][]> testDat = new ArrayList<Expression[][]>();

    private final ArrayList<Expression[][]> testLoc = new ArrayList<Expression[][]>();

    public ImmutableSet<ProgramMethod> getPms() {
	return pms;
    }

    public void setPms(final ImmutableSet<ProgramMethod> pms) {
	this.pms = pms;
    }

    public void addETM(final ExecutionTraceModel[] etm) {
	allETM.add(etm);
    }

    public int nrOfETMs() {
	return allETM.size();
    }

    public int getNodeCount() {
	return nodeCount;
    }

    public void setNodeCount(final int nodeCount) {
	this.nodeCount = nodeCount;
    }

    public Statement[] getCode() {
	return code;
    }

    public void setCode(final Statement[] code) {
	this.code = code;
    }

    public Term getOracle() {
	return oracle;
    }

    public void setOracle(final Term oracle) {
	this.oracle = oracle;
    }

    public LinkedList<ModelGenerator> getMgs() {
	return mgs;
    }

    public void setMgs(final LinkedList<ModelGenerator> mgs) {
	this.mgs = mgs;
    }

    public ImmutableSet<ProgramVariable> getPvs() {
	return pvs;
    }

    public void setPvs(final ImmutableSet<ProgramVariable> pvs) {
	this.pvs = pvs;
    }

    public TestGenerator getTg() {
	return tg;
    }

    public void setTg(final TestGenerator tg) {
	this.tg = tg;
    }

    public ImmutableSet<ProgramVariable> getPvs2() {
	return pvs2;
    }

    public void setPvs2(final ImmutableSet<ProgramVariable> reducedPVSet) {
	this.pvs2 = reducedPVSet;
    }

    public void addTestDat(final Expression[][] tDat) {
	testDat.add(tDat);
    }

    public void addTestLoc(final Expression[][] tLoc) {
	testLoc.add(tLoc);
    }

    public int getNrOfTestDat() {
	return testDat.size();
    }

    public ArrayList<Expression[][]> getTestDat() {
	return testDat;
    }

    public ArrayList<Expression[][]> getTestLoc() {
	return testLoc;
    }

}
