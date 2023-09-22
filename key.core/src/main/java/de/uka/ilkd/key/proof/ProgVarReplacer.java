/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.Iterator;
import java.util.Map;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.visitor.ProgVarReplaceVisitor;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.inst.*;

import org.key_project.util.collection.*;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMapEntry;
import org.key_project.util.collection.ImmutableSet;


/**
 * Replaces program variables.
 */
public final class ProgVarReplacer {

    /**
     * map specifying the replacements to be done
     */
    private final Map<ProgramVariable, ProgramVariable> map;


    /**
     * The services object
     */
    private final Services services;


    /**
     * creates a ProgVarReplacer that replaces program variables as specified by the map parameter
     */
    public ProgVarReplacer(Map<ProgramVariable, ProgramVariable> map, Services services) {
        this.map = map;
        this.services = services;
    }

    /**
     * replaces in a set
     */
    public ImmutableSet<IProgramVariable> replace(ImmutableSet<IProgramVariable> vars) {
        ImmutableSet<IProgramVariable> result = vars;

        for (final IProgramVariable var : vars) {
            IProgramVariable newVar = map.get(var);
            if (newVar != null) {
                result = result.remove(var);
                result = result.add(newVar);
            }
        }

        return result;
    }


    /**
     * replaces in the partially instantiated apps of a taclet index
     */
    public void replace(TacletIndex tacletIndex) {
        ImmutableList<NoPosTacletApp> noPosTacletApps = tacletIndex.getPartialInstantiatedApps();
        ImmutableSet<NoPosTacletApp> appsToBeRemoved, appsToBeAdded;
        appsToBeRemoved = DefaultImmutableSet.nil();
        appsToBeAdded = DefaultImmutableSet.nil();

        for (NoPosTacletApp noPosTacletApp : noPosTacletApps) {
            SVInstantiations insts = noPosTacletApp.instantiations();

            SVInstantiations newInsts = replace(insts);

            if (newInsts != insts) {
                NoPosTacletApp newNoPosTacletApp =
                    NoPosTacletApp.createNoPosTacletApp(noPosTacletApp.taclet(), newInsts,
                        noPosTacletApp.ifFormulaInstantiations(), services);
                appsToBeRemoved = appsToBeRemoved.add(noPosTacletApp);
                appsToBeAdded = appsToBeAdded.add(newNoPosTacletApp);
            }
        }

        tacletIndex.removeTaclets(appsToBeRemoved);
        tacletIndex.addTaclets(appsToBeAdded);
    }


    /**
     * replaces in an SVInstantiations
     */
    public SVInstantiations replace(SVInstantiations insts) {
        SVInstantiations result = insts;

        Iterator<ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>>> it;
        it = insts.pairIterator();
        while (it.hasNext()) {
            ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>> e = it.next();
            SchemaVariable sv = e.key();
            InstantiationEntry<?> ie = e.value();
            Object inst = ie.getInstantiation();

            if (ie instanceof ContextInstantiationEntry) {
                ProgramElement pe = (ProgramElement) inst;
                ProgramElement newPe = replace(pe);
                if (newPe != pe) {
                    ContextInstantiationEntry cie = (ContextInstantiationEntry) ie;
                    result = result.replace(cie.prefix(), cie.suffix(),
                        cie.activeStatementContext(), newPe, services);
                }
            } else if (ie instanceof OperatorInstantiation) {
                /* nothing to be done (currently) */
            } else if (ie instanceof ProgramInstantiation) {
                ProgramElement pe = (ProgramElement) inst;
                ProgramElement newPe = replace(pe);
                if (newPe != pe) {
                    result = result.replace(sv, newPe, services);
                }
            } else if (ie instanceof ProgramListInstantiation) {
                @SuppressWarnings("unchecked")
                ImmutableArray<ProgramElement> a = (ImmutableArray<ProgramElement>) inst;
                int size = a.size();
                ProgramElement[] array = new ProgramElement[size];

                boolean changedSomething = false;
                for (int i = 0; i < size; i++) {
                    ProgramElement pe = a.get(i);
                    array[i] = replace(pe);
                    if (array[i] != pe) {
                        changedSomething = true;
                    }
                }

                if (changedSomething) {
                    ImmutableArray<ProgramElement> newA = new ImmutableArray<>(array);
                    result = result.replace(sv, newA, services);
                }
            } else if (ie instanceof TermInstantiation) {
                Term t = (Term) inst;
                Term newT = replace(t);
                if (newT != t) {
                    result = result.replace(sv, newT, services);
                }
            } else {
                assert false : "unexpected subtype of InstantiationEntry<?>";
            }
        }

        return result;
    }


    /**
     * replaces in a sequent
     */
    public SequentChangeInfo replace(Sequent s) {
        SemisequentChangeInfo anteCI = replace(s.antecedent());
        SemisequentChangeInfo succCI = replace(s.succedent());

        Semisequent newAntecedent = anteCI.semisequent();
        Semisequent newSuccedent = succCI.semisequent();

        Sequent newSequent = Sequent.createSequent(newAntecedent, newSuccedent);

        SequentChangeInfo result =
            SequentChangeInfo.createSequentChangeInfo(anteCI, succCI, newSequent, s);
        return result;
    }


    /**
     * replaces in a semisequent
     */
    public SemisequentChangeInfo replace(Semisequent s) {
        SemisequentChangeInfo result = new SemisequentChangeInfo();
        result.setFormulaList(s.asList());

        final Iterator<SequentFormula> it = s.iterator();

        for (int formulaNumber = 0; it.hasNext(); formulaNumber++) {
            final SequentFormula oldcf = it.next();
            final SequentFormula newcf = replace(oldcf);

            if (newcf != oldcf) {
                result.combine(result.semisequent().replace(formulaNumber, newcf));
            }
        }

        return result;
    }


    /**
     * replaces in a constrained formula
     */
    public SequentFormula replace(SequentFormula cf) {
        SequentFormula result = cf;

        final Term newFormula = replace(cf.formula());

        if (newFormula != cf.formula()) {
            result = new SequentFormula(newFormula);
        }
        return result;
    }


    private Term replaceProgramVariable(Term t) {
        final ProgramVariable pv = (ProgramVariable) t.op();
        ProgramVariable o = map.get(pv);
        if (o instanceof ProgramVariable) {
            return services.getTermFactory().createTerm(o, t.getLabels());
        } else if (o instanceof Term) {
            return (Term) o;
        }
        return t;
    }


    private Term standardReplace(Term t) {
        Term result = t;

        final Term[] newSubTerms = new Term[t.arity()];

        boolean changedSubTerm = false;

        for (int i = 0, ar = t.arity(); i < ar; i++) {
            final Term subTerm = t.sub(i);
            newSubTerms[i] = replace(subTerm);
            if (newSubTerms[i] != subTerm) {
                changedSubTerm = true;
            }
        }

        final JavaBlock jb = t.javaBlock();
        JavaBlock newJb = jb;
        if (!jb.isEmpty()) {
            Statement s = (Statement) jb.program();
            Statement newS = (Statement) replace(s);
            if (newS != s) {
                newJb = JavaBlock.createJavaBlock((StatementBlock) newS);
            }
        }

        if (changedSubTerm || newJb != jb) {
            result = services.getTermFactory().createTerm(t.op(), newSubTerms, t.boundVars(), newJb,
                t.getLabels());
        }
        return result;
    }


    /**
     * replaces in a term
     */
    public Term replace(Term t) {
        final Operator op = t.op();
        if (op instanceof ProgramVariable) {
            return replaceProgramVariable(t);
        } else {
            return standardReplace(t);
        }
    }


    /**
     * replaces in a statement
     */
    public ProgramElement replace(ProgramElement pe) {
        ProgVarReplaceVisitor pvrv = new ProgVarReplaceVisitor(pe, map, false, services);
        pvrv.start();
        return pvrv.result();
    }
}
