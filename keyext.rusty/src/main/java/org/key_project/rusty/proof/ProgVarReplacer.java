/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof;

import java.util.Map;

import org.key_project.logic.PosInTerm;
import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.instantiation.InstantiationEntry;
import org.key_project.prover.sequent.*;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.expr.BlockExpression;
import org.key_project.rusty.ast.visitor.ProgVarReplaceVisitor;
import org.key_project.rusty.logic.*;
import org.key_project.rusty.logic.op.ElementaryUpdate;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.rule.NoPosTacletApp;
import org.key_project.rusty.rule.inst.*;
import org.key_project.util.collection.*;

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
    public ImmutableSet<ProgramVariable> replace(ImmutableSet<ProgramVariable> vars) {
        ImmutableSet<ProgramVariable> result = vars;

        for (final ProgramVariable var : vars) {
            final ProgramVariable newVar = map.get(var);
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
                        noPosTacletApp.assumesFormulaInstantiations(), services);
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

        for (var e : insts.getInstantiationMap()) {
            SchemaVariable sv = e.key();
            InstantiationEntry<?> ie = e.value();
            Object inst = ie.getInstantiation();

            if (ie instanceof ContextInstantiationEntry) {
                var pe = (RustyProgramElement) inst;
                RustyProgramElement newPe = replace(pe);
                if (newPe != pe) {
                    ContextInstantiationEntry cie = (ContextInstantiationEntry) ie;
                    result = result.replace(cie.prefix(), cie.suffix(),
                        newPe, services);
                }
            } /*
               * else if (ie instanceof OperatorInstantiation) {
               * /* nothing to be done (currently)
               */
            /* } */ else if (ie instanceof ProgramInstantiation) {
                var pe = (RustyProgramElement) inst;
                RustyProgramElement newPe = replace(pe);
                if (newPe != pe) {
                    result = result.replace(sv, newPe, services);
                }
            } else if (ie instanceof ProgramListInstantiation) {
                @SuppressWarnings("unchecked")
                var a = (ImmutableArray<RustyProgramElement>) inst;
                int size = a.size();
                var array = new RustyProgramElement[size];

                boolean changedSomething = false;
                for (int i = 0; i < size; i++) {
                    RustyProgramElement pe = a.get(i);
                    array[i] = replace(pe);
                    if (array[i] != pe) {
                        changedSomething = true;
                    }
                }

                if (changedSomething) {
                    ImmutableArray<RustyProgramElement> newA = new ImmutableArray<>(array);
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
     * replaces in a term
     */
    public Term replace(Term t) {
        final Operator op = t.op();
        if (op instanceof ProgramVariable) {
            return replaceProgramVariable(t);
        } else if (op instanceof ElementaryUpdate eu
                && map.containsKey(eu.lhs())) {
            return replaceProgramVariableInLHSOfElementaryUpdate(t);
        } else {
            return standardReplace(t);
        }
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

        Operator op = t.op();
        boolean changedOp = false;
        if (op instanceof Modality mod) {
            var be = (BlockExpression) mod.program().program();
            var newBe = (BlockExpression) replace(be);
            if (newBe != be) {
                var newRb = new RustyBlock(newBe);
                op = Modality.getModality(mod.kind(), newRb);
                changedOp = true;
            }
        }

        if (changedSubTerm || changedOp) {
            result = services.getTermFactory().createTerm(op, newSubTerms,
                (ImmutableArray<QuantifiableVariable>) t.boundVars());
        }
        return result;
    }

    /**
     * replaces in a sequent
     */
    public SequentChangeInfo replace(Sequent s) {
        return replaceInSemisequent(s.succedent(),
            replaceInSemisequent(s.antecedent(), SequentChangeInfo.createSequentChangeInfo(s),
                true),
            false);
    }

    private SequentChangeInfo replaceInSemisequent(Semisequent semi,
            SequentChangeInfo resultInfo,
            boolean inAntec) {
        for (var sf : semi) {
            final SequentFormula newcf = replace(sf);
            if (newcf != sf) {
                final PosInOccurrence pos =
                    new PosInOccurrence(sf, PosInTerm.getTopLevel(), inAntec);
                // radical change need to force rebuild of taclet index, hence, we do not replace
                // but remove and add
                Sequent sequent = resultInfo.sequent();
                resultInfo.combine(
                    sequent.replaceFormula(sequent.formulaNumberInSequent(inAntec, sf), newcf));
            }
        }
        return resultInfo;
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
        if (o != null) {
            return services.getTermFactory().createTerm(o);
        }
        return t;
    }

    /**
     * replaces a program variable on the lefthandside of an elementary update
     * requires the given term to have an elementary update operator as top level operator
     *
     * @param t the Term where to replace renamed variables
     * @return the term with all replacements done
     */
    private Term replaceProgramVariableInLHSOfElementaryUpdate(Term t) {
        final Term newTerm = services.getTermBuilder().elementary(
            map.get(((ElementaryUpdate) t.op()).lhs()),
            standardReplace(t.sub(0)));
        return newTerm;
    }

    /**
     * replaces in a statement
     */
    public RustyProgramElement replace(RustyProgramElement pe) {
        ProgVarReplaceVisitor pvrv = new ProgVarReplaceVisitor(pe, map, false, services);
        pvrv.start();
        return pvrv.result();
    }
}
