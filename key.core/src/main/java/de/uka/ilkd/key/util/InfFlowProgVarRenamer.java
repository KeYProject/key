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
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.VariableNameProposer;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.UpdateableOperator;


/**
 *
 * @author christoph
 */
public class InfFlowProgVarRenamer extends TermBuilder {
    /** The set of terms on which the renaming should be applied. */
    private final JTerm[] terms;

    /**
     * Link between program variables / skolem constants and their renamed counterparts. This map
     * may be pre-initialised.
     */
    private final Map<JTerm, JTerm> replaceMap;

    /**
     * The postfix used for renaming, if a program variable / skolem constant is found which is not
     * yet in the replaceMap.
     */
    private final String postfix;

    /** Goal on which newly created program variables are registered in. */
    private final Goal goalForVariableRegistration;


    public InfFlowProgVarRenamer(JTerm[] terms, Map<JTerm, JTerm> preInitialisedReplaceMap,
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


    public InfFlowProgVarRenamer(JTerm[] terms, String postfix, Goal goalForVariableRegistration,
            Services services) {
        this(terms, null, postfix, goalForVariableRegistration, services);
    }


    public JTerm[] renameVariablesAndSkolemConstants() {
        JTerm[] result = new JTerm[terms.length];
        for (int i = 0; i < terms.length; i++) {
            result[i] = renameVariablesAndSkolemConstants(terms[i]);
        }
        return result;
    }


    private JTerm renameVariablesAndSkolemConstants(JTerm term) {
        final JTerm temp = renameFormulasWithoutPrograms(term);
        final Map<LocationVariable, LocationVariable> progVarReplaceMap =
            restrictToProgramVariables(replaceMap);
        return applyRenamingsToPrograms(temp, progVarReplaceMap);
    }


    private JTerm renameFormulasWithoutPrograms(JTerm term) {
        if (term == null) {
            return null;
        }

        if (!replaceMap.containsKey(term)) {
            renameAndAddToReplaceMap(term);
        }
        return replaceMap.get(term);
    }


    private void renameAndAddToReplaceMap(JTerm term) {
        if (term.op() instanceof ProgramVariable) {
            renameProgramVariable(term);
        } else if (term.op() instanceof Function
                && ((Function) term.op()).isSkolemConstant()) {
            renameSkolemConstant(term);
        } else if (term.op() instanceof ElementaryUpdate) {
            applyRenamingsOnUpdate(term);
        } else {
            applyRenamingsOnSubterms(term);
        }
    }


    private void renameProgramVariable(JTerm term) {
        assert term.arity() == 0;
        final ProgramVariable pv = (ProgramVariable) term.op();
        final Name newName =
            VariableNameProposer.DEFAULT.getNewName(services, new Name(pv.name() + postfix));
        final ProgramVariable renamedPv = rename(newName, pv);

        // for the taclet application dialog (which gets the declared
        // program variables in a strange way and not directly from the
        // namespace); adds the renamedPv also to the namespace
        goalForVariableRegistration.addProgramVariable(renamedPv);

        final JTerm pvTerm = label(var(renamedPv), term.getLabels());
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


    private void renameSkolemConstant(JTerm term) {
        final Function f = (Function) term.op();
        final Name newName =
            VariableNameProposer.DEFAULT.getNewName(services, new Name(f.name() + postfix));
        final Function renamedF = new JFunction(newName, f.sort(), f.argSorts(),
            f.whereToBind(), f.isUnique(), f.isSkolemConstant());
        services.getNamespaces().functions().addSafely(renamedF);
        final JTerm fTerm = label(func(renamedF), term.getLabels());
        replaceMap.put(term, fTerm);
    }


    private void applyRenamingsOnUpdate(JTerm term) {
        final ElementaryUpdate u = (ElementaryUpdate) term.op();
        final JTerm lhsTerm = varOfUpdateableOp(u.lhs());
        final JTerm renamedLhs = renameFormulasWithoutPrograms(lhsTerm);
        final JTerm[] renamedSubs = renameSubs(term);
        final ElementaryUpdate renamedU =
            ElementaryUpdate.getInstance((UpdateableOperator) renamedLhs.op());
        final JTerm uTerm = label(tf().createTerm(renamedU, renamedSubs), term.getLabels());
        replaceMap.put(term, uTerm);
    }


    private void applyRenamingsOnSubterms(JTerm term) {
        final JTerm[] renamedSubs = renameSubs(term);
        final JTerm renamedTerm = tf().createTerm(term.op(), renamedSubs, term.boundVars(),
            term.getLabels());
        replaceMap.put(term, renamedTerm);
    }


    private JTerm[] renameSubs(JTerm term) {
        JTerm[] renamedSubs = new JTerm[term.arity()];
        for (int i = 0; i < renamedSubs.length; i++) {
            renamedSubs[i] = renameFormulasWithoutPrograms(term.sub(i));
        }
        return renamedSubs;
    }


    private JTerm applyRenamingsToPrograms(JTerm term,
            Map<LocationVariable, LocationVariable> progVarReplaceMap) {

        if (term == null) {
            return null;
        } else if (term.op() instanceof JModality mod) {
            final JavaBlock renamedJavaBlock =
                renameJavaBlock(progVarReplaceMap, mod.programBlock().program(), services);
            final JTerm[] appliedSubs = applyProgramRenamingsToSubs(term, progVarReplaceMap);

            return tf().createTerm(JModality.getModality(mod.kind(), renamedJavaBlock), appliedSubs,
                term.boundVars(),
                term.getLabels());
        } else {
            return term;
        }
    }


    private JTerm[] applyProgramRenamingsToSubs(JTerm term,
            Map<LocationVariable, LocationVariable> progVarReplaceMap) {
        JTerm[] appliedSubs = new JTerm[term.arity()];
        for (int i = 0; i < appliedSubs.length; i++) {
            appliedSubs[i] = applyRenamingsToPrograms(term.sub(i), progVarReplaceMap);
        }
        return appliedSubs;
    }


    private JavaBlock renameJavaBlock(Map<LocationVariable, LocationVariable> progVarReplaceMap,
            JavaProgramElement program, Services services) {
        final ProgVarReplaceVisitor paramRepl =
            new ProgVarReplaceVisitor(program, progVarReplaceMap, services);
        paramRepl.start();
        final JavaBlock renamedJavaBlock =
            JavaBlock.createJavaBlock((StatementBlock) paramRepl.result());
        return renamedJavaBlock;
    }


    private Map<LocationVariable, LocationVariable> restrictToProgramVariables(
            Map<JTerm, JTerm> replaceMap) {
        Map<LocationVariable, LocationVariable> progVarReplaceMap =
            new HashMap<>();
        for (final JTerm t : replaceMap.keySet()) {
            if (t.op() instanceof LocationVariable lv) {
                progVarReplaceMap.put(lv,
                    (LocationVariable) replaceMap.get(t).op());
            }
        }
        return progVarReplaceMap;
    }
}
