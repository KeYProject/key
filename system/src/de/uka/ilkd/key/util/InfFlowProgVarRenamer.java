/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.util;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.visitor.ProgVarReplaceVisitor;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateableOperator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.VariableNameProposer;
import java.util.HashMap;
import java.util.Map;


/**
 *
 * @author christoph
 */
public class InfFlowProgVarRenamer extends TermBuilder {
    /** The set of terms on which the renaming should be applied. */
    private final Term[] terms;

    /** Link between program variables / skolem constants and their renamed
     *  counterparts. This map may be pre-initialised.
     */
    private final Map<Term, Term> replaceMap;

    /** The postfix used for renaming, if a program variable / skolem constant
     *  is found which is not yet in the replaceMap.
     */
    private final String postfix;

    /** Goal on which newly created program variables are registered in. */
    private final Goal goalForVariableRegistration;


    public InfFlowProgVarRenamer(Term[] terms,
                                 Map<Term, Term> preInitialisedReplaceMap,
                                 String postfix,
                                 Goal goalForVariableRegistration,
                                 Services services) {
        super(services.getTermFactory(), services);
        this.terms = terms;
        this.postfix = postfix;
        this.goalForVariableRegistration = goalForVariableRegistration;
        if (preInitialisedReplaceMap == null) {
            this.replaceMap = new HashMap<Term, Term>();
        } else {
            this.replaceMap = preInitialisedReplaceMap;
        }

        // the built-in heap symbol has to be handled with care; it is safer
        // not to replace it
        this.replaceMap.put(getBaseHeap(), getBaseHeap());
    }
    

    public InfFlowProgVarRenamer(Term[] terms,
                                 String postfix,
                                 Goal goalForVariableRegistration,
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
        } else if (term.op() instanceof Function &&
                   ((Function) term.op()).isSkolemConstant()) {
            renameSkolemConstant(term);
        } else if (term.op() instanceof ElementaryUpdate) {
            applyRenamingsOnUpdate(term);
        } else {
            applyRenamingsOnSubterms(term);
        }
    }


    private void renameProgramVariable(Term term) {
        assert term.subs().isEmpty();
        final ProgramVariable pv = (ProgramVariable) term.op();
        final Name newName =
                VariableNameProposer.DEFAULT.getNewName(services,
                                                        new Name(pv.name() +
                                                                 postfix));
        final Operator renamedPv = pv.rename(newName);

        // for the taclet application dialog (which gets the declared
        // program variables in a strange way and not directly from the
        // namespace); adds the renamedPv also to the namespace
        goalForVariableRegistration.addProgramVariable((ProgramVariable)renamedPv);

        final Term pvTerm = label(var((ProgramVariable)renamedPv),
                                  term.getLabels());
        replaceMap.put(term, pvTerm);
    }


    private void renameSkolemConstant(Term term) {
        final Function f = (Function) term.op();
        final Name newName =
                VariableNameProposer.DEFAULT.getNewName(services,
                                                        new Name(f.name() +
                                                                 postfix));
        final Function renamedF = f.rename(newName);
        services.getNamespaces().functions().addSafely(renamedF);
        final Term fTerm =
                label(func(renamedF),
                      term.getLabels());
        replaceMap.put(term, fTerm);
    }


    private void applyRenamingsOnUpdate(Term term) {
        final ElementaryUpdate u = (ElementaryUpdate) term.op();
        final Term lhsTerm = var(u.lhs());
        final Term renamedLhs = renameFormulasWithoutPrograms(lhsTerm);
        final Term[] renamedSubs = renameSubs(term);
        final ElementaryUpdate renamedU =
                ElementaryUpdate.getInstance((UpdateableOperator) renamedLhs.op());
        final Term uTerm =
                label(tf().createTerm(renamedU, renamedSubs),
                      term.getLabels());
        replaceMap.put(term, uTerm);
    }


    private void applyRenamingsOnSubterms(Term term) {
        final Term[] renamedSubs = renameSubs(term);
        final Term renamedTerm =
                tf().createTerm(term.op(), renamedSubs,
                                term.boundVars(), term.javaBlock(),
                                term.getLabels());
        replaceMap.put(term, renamedTerm);
    }


    private Term[] renameSubs(Term term) {
        Term[] renamedSubs = null;
        if (term.subs() != null) {
            renamedSubs = new Term[term.subs().size()];
            for (int i = 0; i < renamedSubs.length; i++) {
                renamedSubs[i] = renameFormulasWithoutPrograms(term.sub(i));
            }
        }
        return renamedSubs;
    }


    private Term applyRenamingsToPrograms(Term term,
                                          Map<ProgramVariable, ProgramVariable> progVarReplaceMap) {

        if (term != null) {
            final JavaBlock renamedJavaBlock =
                    renameJavaBlock(progVarReplaceMap, term, services);
            final Term[] appliedSubs =
                    applyProgramRenamingsToSubs(term, progVarReplaceMap);

            final Term renamedTerm =
                    tf().createTerm(term.op(), appliedSubs,
                                    term.boundVars(), renamedJavaBlock,
                                    term.getLabels());
            return renamedTerm;
        } else {
            return null;
        }
    }


    private Term[] applyProgramRenamingsToSubs(Term term,
                                               Map<ProgramVariable, ProgramVariable> progVarReplaceMap) {
        Term[] appliedSubs = null;
        if (term.subs() != null) {
            appliedSubs = new Term[term.subs().size()];
            for (int i = 0; i < appliedSubs.length; i++) {
                appliedSubs[i] = applyRenamingsToPrograms(term.sub(i),
                                                          progVarReplaceMap);
            }
        }
        return appliedSubs;
    }


    private JavaBlock renameJavaBlock(Map<ProgramVariable, ProgramVariable> progVarReplaceMap,
                                      Term term, Services services) {
        final ProgVarReplaceVisitor paramRepl =
                new ProgVarReplaceVisitor(term.javaBlock().program(), progVarReplaceMap, services);
        paramRepl.start();
        final JavaBlock renamedJavaBlock =
                JavaBlock.createJavaBlock((StatementBlock) paramRepl.result());
        return renamedJavaBlock;
    }


    private Map<ProgramVariable, ProgramVariable>
                        restrictToProgramVariables(Map<Term, Term> replaceMap) {
        Map<ProgramVariable, ProgramVariable> progVarReplaceMap =
                new HashMap<ProgramVariable, ProgramVariable>();
        for (final Term t : replaceMap.keySet()) {
            if (t.op() instanceof ProgramVariable) {
                progVarReplaceMap.put((ProgramVariable) t.op(),
                                      (ProgramVariable) replaceMap.get(t).op());
            }
        }
        return progVarReplaceMap;
    }
}
