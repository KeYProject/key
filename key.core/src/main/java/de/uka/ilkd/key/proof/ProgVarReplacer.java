/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.Map;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.visitor.ProgVarReplaceVisitor;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.inst.*;

import org.key_project.logic.PosInTerm;
import org.key_project.logic.op.Modality;
import org.key_project.logic.op.Operator;
import org.key_project.prover.rules.instantiation.InstantiationEntry;
import org.key_project.prover.rules.instantiation.ListInstantiation;
import org.key_project.prover.sequent.*;
import org.key_project.util.collection.*;


/**
 * Replaces program variables.
 */
public final class ProgVarReplacer {

    /**
     * map specifying the replacements to be done
     */
    private final Map<LocationVariable, LocationVariable> map;

    /**
     * The services object
     */
    private final Services services;

    /**
     * creates a ProgVarReplacer that replaces program variables as specified by the map parameter
     */
    public ProgVarReplacer(Map<LocationVariable, LocationVariable> map, Services services) {
        this.map = map;
        this.services = services;
    }

    /**
     * replaces in a set
     */
    public ImmutableSet<IProgramVariable> replace(ImmutableSet<IProgramVariable> vars) {
        ImmutableSet<IProgramVariable> result = vars;

        for (final IProgramVariable var : vars) {
            final IProgramVariable newVar = map.get(var);
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
        final var noPosTacletApps = tacletIndex.getPartialInstantiatedApps();
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
            var sv = e.key();
            InstantiationEntry<?> ie = e.value();
            Object inst = ie.getInstantiation();

            if (inst instanceof JTerm t) {
                final JTerm newT = replace(t);
                if (newT != t) {
                    result = result.replace(sv, newT, services);
                }
            } else if (inst instanceof ContextStatementBlockInstantiation cie) {
                final ProgramElement pe = cie.program();
                final ProgramElement newPe = replace(pe);
                if (newPe != pe) {
                    result = result.replace(cie.prefix(), cie.suffix(),
                        cie.activeStatementContext(), newPe, services);
                }
            } else if (inst instanceof Operator) {
                /* nothing to be done (currently) */
            } else if (inst instanceof ProgramElement pe) {
                final ProgramElement newPe = replace(pe);
                if (newPe != pe) {
                    result = result.replace(sv, newPe, services);
                }
            } else if (ie instanceof ListInstantiation<?> list) {
                if (list.getType() != ProgramElement.class) {
                    throw new RuntimeException("Unexpected list instantiation: " + ie);
                }
                final ImmutableArray<ProgramElement> a = (ImmutableArray<ProgramElement>) inst;
                final int size = a.size();
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
                    result = result.replace(sv, new ImmutableArray<>(array), services);
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

        final JTerm newFormula = replace((JTerm) cf.formula());

        if (newFormula != cf.formula()) {
            result = new SequentFormula(newFormula);
        }
        return result;
    }

    private JTerm replaceProgramVariable(JTerm t) {
        final ProgramVariable pv = (ProgramVariable) t.op();
        ProgramVariable o = map.get(pv);
        if (o != null) {
            return services.getTermFactory().createTerm(o, t.getLabels());
        }
        return t;
    }

    private JTerm standardReplace(JTerm t) {
        JTerm result = t;

        final JTerm[] newSubTerms = new JTerm[t.arity()];

        boolean changedSubTerm = false;

        for (int i = 0, ar = t.arity(); i < ar; i++) {
            final JTerm subTerm = t.sub(i);
            if (subTerm.isRigid()) {
                newSubTerms[i] = subTerm;
            } else {
                newSubTerms[i] = replace(subTerm);
                if (newSubTerms[i] != subTerm) {
                    changedSubTerm = true;
                }
            }
        }

        Operator op = t.op();

        // TODO (DD): Clean up
        final JavaBlock jb = t.javaBlock();
        JavaBlock newJb = jb;
        if (op instanceof Modality mod) {
            Statement s = (Statement) jb.program();
            Statement newS = (Statement) replace(s);
            if (newS != s) {
                newJb = JavaBlock.createJavaBlock((StatementBlock) newS);
                op = JModality.getModality(mod.kind(), newJb);
            }
        }

        if (changedSubTerm || newJb != jb) {
            result = services.getTermFactory().createTerm(op, newSubTerms, t.boundVars(),
                t.getLabels());
        }
        return result;
    }

    /**
     * replaces in a term
     */
    public JTerm replace(JTerm t) {
        final Operator op = t.op();
        if (op instanceof ProgramVariable) {
            return replaceProgramVariable(t);
        } else if (op instanceof ElementaryUpdate
                && map.containsKey(((ElementaryUpdate) op).lhs())) {
            return replaceProgramVariableInLHSOfElementaryUpdate(t);
        } else {
            return standardReplace(t);
        }
    }

    /**
     * replaces a program variable on the lefthandside of an elementary update
     * requires the given term to have an elementary update operator as top level operator
     *
     * @param t the Term where to replace renamed variables
     * @return the term with all replacements done
     */
    private JTerm replaceProgramVariableInLHSOfElementaryUpdate(JTerm t) {
        final JTerm newTerm = services.getTermBuilder().elementary(
            map.get(((ElementaryUpdate) t.op()).lhs()),
            standardReplace(t.sub(0)));
        return newTerm;
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
