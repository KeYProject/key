/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.visitor.ProgVarReplaceVisitor;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.VariableNameProposer;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;


/**
 *
 * @author christoph
 */
public class InfFlowProgVarRenamer extends TermBuilder {
    /** The set of terms on which the renaming should be applied. */
    private final Term[] terms;

    /**
     * Link between program variables / skolem constants and their renamed counterparts. This map
     * may be pre-initialised.
     */
    private final Map<Term, Term> replaceMap;

    /**
     * The postfix used for renaming, if a program variable / skolem constant is found which is not
     * yet in the replaceMap.
     */
    private final String postfix;

    /** Goal on which newly created program variables are registered in. */
    private final Goal goalForVariableRegistration;


    public InfFlowProgVarRenamer(Term[] terms, Map<Term, Term> preInitialisedReplaceMap,
            String postfix, Goal goalForVariableRegistration, Services services) {
        super(services.getTermFactory(), services);
        this.terms = terms;
        this.postfix = postfix;
        this.goalForVariableRegistration = goalForVariableRegistration;
        if (preInitialisedReplaceMap == null) {
            this.replaceMap = new HashMap<>();
        } else {
            this.replaceMap = preInitialisedReplaceMap;
        }

        // the built-in heap symbol has to be handled with care; it is safer
        // not to replace it
        this.replaceMap.put(getBaseHeap(), getBaseHeap());
    }


    public InfFlowProgVarRenamer(Term[] terms, String postfix, Goal goalForVariableRegistration,
            Services services) {
        this(terms, null, postfix, goalForVariableRegistration, services);
    }


    public Term[] renameVariablesAndSkolemConstants() {
        Term[] result = new Term[terms.length];
        for (int i = 0; i < terms.length; i++) {
            result[i] = renameVariablesAndSkolemConstants(terms[i]);
        }
        return result;
    }


    private Term renameVariablesAndSkolemConstants(Term term) {
        final Term temp = renameFormulasWithoutPrograms(term);
        final Map<ProgramVariable, ProgramVariable> progVarReplaceMap =
            restrictToProgramVariables(replaceMap);
        return applyRenamingsToPrograms(temp, progVarReplaceMap);
    }


    private Term renameFormulasWithoutPrograms(Term term) {
        if (term == null) {
            return null;
        }

        if (!replaceMap.containsKey(term)) {
            renameAndAddToReplaceMap(term);
        }
        return replaceMap.get(term);
    }


    private void renameAndAddToReplaceMap(Term term) {
        if (term.op() instanceof ProgramVariable) {
            renameProgramVariable(term);
        } else if (term.op() instanceof JFunction
                && ((Function) term.op()).isSkolemConstant()) {
            renameSkolemConstant(term);
        } else if (term.op() instanceof ElementaryUpdate) {
            applyRenamingsOnUpdate(term);
        } else {
            applyRenamingsOnSubterms(term);
        }
    }


    private void renameProgramVariable(Term term) {
        assert term.arity() == 0;
        final ProgramVariable pv = (ProgramVariable) term.op();
        final Name newName =
            VariableNameProposer.DEFAULT.getNewName(services, new Name(pv.name() + postfix));
        final ProgramVariable renamedPv = rename(newName, pv);

        // for the taclet application dialog (which gets the declared
        // program variables in a strange way and not directly from the
        // namespace); adds the renamedPv also to the namespace
        goalForVariableRegistration.addProgramVariable(renamedPv);

        final Term pvTerm = label(var(renamedPv), term.getLabels());
        replaceMap.put(term, pvTerm);
    }

    /**
     * Returns an equivalent variable with the new name.
     *
     * @param newName the new name
     * @param pv the program variable to be renamed
     * @return equivalent operator with the new name
     */
    public static ProgramVariable rename(Name newName, ProgramVariable pv) {
        if (pv instanceof LocationVariable lv) {
            if (lv.getKeYJavaType() != null) {
                return new LocationVariable(new ProgramElementName(newName.toString()),
                    lv.getKeYJavaType(),
                    lv.getContainerType(), lv.isStatic(), lv.isModel());
            } else {
                return new LocationVariable(new ProgramElementName(newName.toString()), lv.sort());
            }
        } else if (pv instanceof ProgramConstant pc) {
            return new ProgramConstant(new ProgramElementName(newName.toString()),
                pc.getKeYJavaType(),
                pc.getContainerType(), pc.isStatic(), pc.getCompileTimeConstant());
        } else {
            throw new IllegalArgumentException("Unknown type for pv: " + pv);
        }

    }


    private void renameSkolemConstant(Term term) {
        final Function f = (Function) term.op();
        final Name newName =
            VariableNameProposer.DEFAULT.getNewName(services, new Name(f.name() + postfix));
        final JFunction renamedF = new JFunction(newName, f.sort(), f.argSorts(),
            f.whereToBind(), f.isUnique(), f.isSkolemConstant());
        services.getNamespaces().functions().addSafely(renamedF);
        final Term fTerm = label(func(renamedF), term.getLabels());
        replaceMap.put(term, fTerm);
    }


    private void applyRenamingsOnUpdate(Term term) {
        final ElementaryUpdate u = (ElementaryUpdate) term.op();
        final Term lhsTerm = var(u.lhs());
        final Term renamedLhs = renameFormulasWithoutPrograms(lhsTerm);
        final Term[] renamedSubs = renameSubs(term);
        final ElementaryUpdate renamedU =
            ElementaryUpdate.getInstance((UpdateableOperator) renamedLhs.op());
        final Term uTerm = label(tf().createTerm(renamedU, renamedSubs), term.getLabels());
        replaceMap.put(term, uTerm);
    }


    private void applyRenamingsOnSubterms(Term term) {
        final Term[] renamedSubs = renameSubs(term);
        final Term renamedTerm = tf().createTerm(term.op(), renamedSubs, term.boundVars(),
            term.getLabels());
        replaceMap.put(term, renamedTerm);
    }


    private Term[] renameSubs(Term term) {
        Term[] renamedSubs = new Term[term.arity()];
        for (int i = 0; i < renamedSubs.length; i++) {
            renamedSubs[i] = renameFormulasWithoutPrograms(term.sub(i));
        }
        return renamedSubs;
    }


    private Term applyRenamingsToPrograms(Term term,
            Map<ProgramVariable, ProgramVariable> progVarReplaceMap) {

        if (term == null) {
            return null;
        } else if (term.op() instanceof Modality mod) {
            final JavaBlock renamedJavaBlock =
                renameJavaBlock(progVarReplaceMap, mod.program().program(), services);
            final Term[] appliedSubs = applyProgramRenamingsToSubs(term, progVarReplaceMap);

            return tf().createTerm(Modality.getModality(mod.kind(), renamedJavaBlock), appliedSubs,
                term.boundVars(),
                term.getLabels());
        } else {
            return term;
        }
    }


    private Term[] applyProgramRenamingsToSubs(Term term,
            Map<ProgramVariable, ProgramVariable> progVarReplaceMap) {
        Term[] appliedSubs = new Term[term.arity()];
        for (int i = 0; i < appliedSubs.length; i++) {
            appliedSubs[i] = applyRenamingsToPrograms(term.sub(i), progVarReplaceMap);
        }
        return appliedSubs;
    }


    private JavaBlock renameJavaBlock(Map<ProgramVariable, ProgramVariable> progVarReplaceMap,
            JavaProgramElement program, Services services) {
        final ProgVarReplaceVisitor paramRepl =
            new ProgVarReplaceVisitor(program, progVarReplaceMap, services);
        paramRepl.start();
        final JavaBlock renamedJavaBlock =
            JavaBlock.createJavaBlock((StatementBlock) paramRepl.result());
        return renamedJavaBlock;
    }


    private Map<ProgramVariable, ProgramVariable> restrictToProgramVariables(
            Map<Term, Term> replaceMap) {
        Map<ProgramVariable, ProgramVariable> progVarReplaceMap =
            new HashMap<>();
        for (final Term t : replaceMap.keySet()) {
            if (t.op() instanceof ProgramVariable) {
                progVarReplaceMap.put((ProgramVariable) t.op(),
                    (ProgramVariable) replaceMap.get(t).op());
            }
        }
        return progVarReplaceMap;
    }
}
