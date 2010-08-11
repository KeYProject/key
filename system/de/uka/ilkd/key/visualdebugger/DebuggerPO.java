// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.visualdebugger;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.proof.BuiltInRuleIndex;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ModStrategy;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
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

    private Term createConjunction(ImmutableList<Term> list) {
        Term result = null;
        for (Iterator<Term> it = list.iterator(); it.hasNext();) {
            result = (result == null ? it.next() : 
                TermFactory.DEFAULT.createJunctorTerm(Op.AND, result, it.next()));
        }
        return result == null ? TermFactory.DEFAULT.createJunctorTerm(Op.TRUE) : 
            result;
    }

    public String getJavaPath() throws ProofInputException {
        return null;
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

    private ImmutableList<Term> getTerms(ImmutableList<ConstrainedFormula> list) {
        ImmutableList<Term> result = ImmutableSLList.<Term>nil();
        for (ConstrainedFormula aList : list) {
            result = result.append(aList.formula());
        }
        return result;
    }


    public void initJavaModelSettings(String classPath) {

    }

    private Term list2term(ImmutableList<Term> list) {
        Term result = null;
        for (Term t : list) {
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

    public void readActivatedChoices() {
    }

    public void readProblem(ModStrategy mod) {
    }
    
    public boolean implies(ProofOblInput po) {
        return equals(po);
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


    public void setPCImpl(ImmutableList<Term> l1, ImmutableList<Term> l2) {
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

    public void setSpecFormula(ImmutableList<Term> specFormula) {
        Term result = null;
        for (Term t : specFormula) {
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
                ant.toList()).toArray(new Term[ant.size()]));
        Term b = TermFactory.DEFAULT.createJunctorTerm(Op.OR, getTerms(
                succ.toList()).toArray(new Term[succ.size()]));
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

    public void setTerms(ImmutableList<Term> terms) {
        specFormula = TermFactory.DEFAULT
          .createJunctorTerm(Op.NOT, createConjunction(terms));
    }

    public void setUp(Sequent precondition, ITNode n) {
        Sequent result = precondition;
        for (Term t : n.getPc(true)) {
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

    public void setUp(Sequent precondition, ITNode n, ImmutableSet<Term> indexConf) {
        this.setUp(precondition, n);
        for (Term t : indexConf) {
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

    public void setUp(Sequent precondition, ITNode n, ImmutableSet<Term> indexConf,
            Term post) {
        this.setUp(precondition, n, indexConf);
        sequent = sequent.addFormula(
                new ConstrainedFormula(post, Constraint.BOTTOM), false, true)
                .sequent();

    }
}
