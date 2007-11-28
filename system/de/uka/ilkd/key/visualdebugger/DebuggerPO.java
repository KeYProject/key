// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.visualdebugger;

import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.proof.BuiltInRuleIndex;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.mgt.Contract;
import de.uka.ilkd.key.proof.mgt.Contractable;
import de.uka.ilkd.key.visualdebugger.executiontree.ITNode;

public class DebuggerPO implements ProofOblInput {

    private BuiltInRuleIndex builtInRules;

    /** the init config of the mainof */
    private InitConfig initConfig;

    /** the name of the po */
    private String name;

    /** the proof aggregate for this proof obligation */
    private ProofAggregate po;

    private Sequent sequent = null;

    private ProofSettings settings;

    /** the formula used for specification computation of the body */
    private Term specFormula = null;// TermFactory.DEFAULT.createJunctorTerm(Op.TRUE);

    private TacletIndex taclets;

    /**
     * creates an instance of this proof obligation
     * 
     * @param name
     *                a String with a short describing name what is computed
     */
    public DebuggerPO(String name) {
        this.name = name;
    }

    public boolean askUserForEnvironment() {
        return false;
    }

    private Term createConjunction(ListOfTerm list) {
        Term result = null;
        for (IteratorOfTerm it = list.iterator(); it.hasNext();) {
            Term t = it.next();
            if (result == null)
                result = t;
            else
                result = TermFactory.DEFAULT.createJunctorTerm(Op.AND, result,
                        t);

        }
        if (result == null)
            result = TermFactory.DEFAULT.createJunctorTerm(Op.TRUE);
        return result;

    }

    public String getJavaPath() throws ProofInputException {
        return null;
    }

    public Contractable[] getObjectOfContract() {
        return new Contractable[0];
    }

    /**
     * returns the proof to be loaded in the prover
     */
    public ProofAggregate getPO() {
        if (po == null) {
            if ((specFormula == null && sequent == null) || taclets == null
                    || builtInRules == null || initConfig == null
                    || settings == null) {
                throw new IllegalStateException("Loop specification proof "
                        + "obligation is not initialized completely.");
            }

            Proof proof = null;
            if (specFormula != null)
                proof = new Proof(name, specFormula, "", taclets, builtInRules,
                        initConfig.getServices(), settings);
            else if (sequent != null) {
                proof = new Proof(name, sequent, "", taclets, builtInRules,
                        initConfig.getServices(), settings);
            }
            proof.setSimplifier(settings
                    .getSimultaneousUpdateSimplifierSettings().getSimplifier());
            po = ProofAggregate.createProofAggregate(proof, name);

        }
        return po;
    }

    private ListOfTerm getTerms(ListOfConstrainedFormula list) {
        ListOfTerm result = SLListOfTerm.EMPTY_LIST;
        for (IteratorOfConstrainedFormula it = list.iterator(); it.hasNext();) {
            result = result.append(it.next().formula());
        }
        return result;
    }

    public boolean initContract(Contract ct) {
        // TODO Auto-generated method stub
        return false;
    }

    public void initJavaModelSettings(String classPath) {

    }

    private Term list2term(ListOfTerm list) {
        Term result = null;
        for (IteratorOfTerm it = list.iterator(); it.hasNext();) {
            Term t = it.next();
            t = TermFactory.DEFAULT.createJunctorTerm(Op.NOT, t);
            if (result == null)
                result = t;
            else
                result = TermFactory.DEFAULT.createJunctorTerm(Op.AND, result,
                        t);

        }
        if (result == null)
            result = TermFactory.DEFAULT.createJunctorTerm(Op.TRUE);
        return result;

    }

    public String name() {
        return name;
    }

    // all below are not used for this proof obligation
    public void read(ModStrategy mod) {
    }

    public void readActivatedChoices() {
    }

    public Includes readIncludes() throws ProofInputException {
        return null;
    }

    public String readModel() throws ProofInputException {
        return null;
    }

    public void readProblem(ModStrategy mod) {
    }

    public void readSpecs() {
    }

    /**
     * the initial config containing for example the services which provide
     * access to the Java model
     */
    public void setConfig(InitConfig i) {
        this.initConfig = i;
    }

    /**
     * the indices with the rules to be used for specification computation
     * 
     * @param taclets
     *                the TacletIndex with the taclet rule base to be used
     * @param builtInRules
     *                the BuiltInRuleIndex with all available built-in rules
     */
    public void setIndices(TacletIndex taclets, BuiltInRuleIndex builtInRules) {
        this.taclets = taclets;
        this.builtInRules = builtInRules;
    }

    public void setInitConfig(InitConfig i) {
        // TODO Auto-generated method stub

    }

    public void setPCImpl(ListOfTerm l1, ListOfTerm l2) {
        Term t1 = list2term(l1);
        Term t2 = list2term(l2);
        specFormula = TermFactory.DEFAULT.createJunctorTerm(Op.IMP, new Term[] {
                t1, t2 });
    }

    /**
     * the proof settings to be used
     * 
     * @param settings
     *                the ProofSettings to be used for e.g. the update
     *                simplifier to be taken
     */
    public void setProofSettings(ProofSettings settings) {
        this.settings = settings;
    }

    public void setSequent(Sequent s) {
        this.sequent = s;
    }

    public void setSpecFormula(ListOfTerm specFormula) {
        Term result = null;
        for (IteratorOfTerm it = specFormula.iterator(); it.hasNext();) {
            Term t = it.next();
            t = TermFactory.DEFAULT.createJunctorTerm(Op.NOT, t);
            if (result == null)
                result = t;
            else
                result = TermFactory.DEFAULT.createJunctorTerm(Op.AND, result,
                        t);
        }
        this.specFormula = result;
    }

    public void setSpecFormula(Sequent s) {
        Semisequent ant = s.antecedent();
        Semisequent succ = s.succedent();

        Term a = TermFactory.DEFAULT.createJunctorTerm(Op.AND, getTerms(
                ant.toList()).toArray());
        Term b = TermFactory.DEFAULT.createJunctorTerm(Op.OR, getTerms(
                succ.toList()).toArray());
        specFormula = TermFactory.DEFAULT.createJunctorTerm(Op.IMP, a, b);
    }

    /**
     * the formula with the program whose specification has to be computed
     * 
     * @param specFormula
     *                the Term to be loaded
     */
    public void setSpecFormula(Term specFormula) {
        this.specFormula = specFormula;
    }

    public void setTerms(ListOfTerm terms) {
        this.specFormula = this.createConjunction(terms);
        specFormula = TermFactory.DEFAULT
                .createJunctorTerm(Op.NOT, specFormula);
    }

    public void setUp(Sequent precondition, ITNode n) {
        Sequent result = precondition;
        for (IteratorOfTerm it = n.getPc(true).iterator(); it.hasNext();) {
            Term t = it.next();
            if (t.op() == Op.NOT)
                result = result.addFormula(
                        new ConstrainedFormula(t.sub(0), Constraint.BOTTOM),
                        false, true).sequent();
            else
                result = result.addFormula(
                        new ConstrainedFormula(t, Constraint.BOTTOM), true,
                        true).sequent();

        }
        this.sequent = result;
    }

    public void setUp(Sequent precondition, ITNode n, SetOfTerm indexConf) {
        this.setUp(precondition, n);
        for (IteratorOfTerm it = indexConf.iterator(); it.hasNext();) {
            Term t = it.next();
            if (t.op() == Op.NOT)
                this.sequent = sequent.addFormula(
                        new ConstrainedFormula(t.sub(0), Constraint.BOTTOM),
                        false, true).sequent();
            else
                sequent = sequent.addFormula(
                        new ConstrainedFormula(t, Constraint.BOTTOM), true,
                        true).sequent();
        }
    }

    public void setUp(Sequent precondition, ITNode n, SetOfTerm indexConf,
            Term post) {
        this.setUp(precondition, n, indexConf);
        sequent = sequent.addFormula(
                new ConstrainedFormula(post, Constraint.BOTTOM), false, true)
                .sequent();

    }

    public void startProtocol() {
    }

}
