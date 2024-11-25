/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.speclang;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.function.UnaryOperator;

import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.abstraction.KeYRustyType;
import org.key_project.rusty.logic.RustyDLTheory;
import org.key_project.rusty.logic.TermBuilder;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.ProgramFunction;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.proof.OpReplacer;
import org.key_project.util.collection.ImmutableList;

import static org.key_project.rusty.util.Assert.assertSubSort;

/**
 * Standard implementation of the OperationContract interface.
 */
public class FunctionalOperationContractImpl implements FunctionalOperationContract {
    final String baseName;
    final String name;
    final KeYRustyType krt;
    final ProgramFunction fn;
    final Modality.RustyModalityKind modalityKind;
    /**
     * The original precondition terms.
     */
    final Term originalPre;
    final Term originalMby;
    /**
     * The original postcondition term.
     */
    final Term originalPost;
    /**
     * The original modifiable clause term.
     */
    final Term originalModifiable;
    final ImmutableList<ProgramVariable> originalParamVars;
    final ProgramVariable originalResultVar;
    final Term globalDefs;
    final int id;
    final boolean toBeSaved;

    /**
     * The term builder.
     */
    private final TermBuilder tb;
    /**
     * The services object.
     */
    private final Services services;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    FunctionalOperationContractImpl(String baseName, String name, KeYRustyType krt,
            ProgramFunction fn, Modality.RustyModalityKind modalityKind,
            Term pres, Term mby, Term posts, Term modifiables,
            ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar, Term globalDefs,
            int id, boolean toBeSaved,
            Services services) {
        assert !(name == null && baseName == null);
        assert krt != null;
        assert fn != null;
        assert modalityKind != null;
        assert pres != null;
        assert posts != null;
        assert globalDefs == null || globalDefs.sort() == RustyDLTheory.UPDATE;
        assert paramVars != null;
        assert paramVars.size() == fn.getNumParams();
        assert services != null;
        this.services = services;
        tb = services.getTermBuilder();
        this.baseName = baseName;
        this.name = name;
        this.fn = fn;
        this.krt = krt;
        this.modalityKind = modalityKind;
        this.originalPre = pres;
        this.originalMby = mby;
        this.originalPost = posts;
        this.originalModifiable = modifiables;
        this.originalParamVars = paramVars;
        this.originalResultVar = resultVar;
        this.globalDefs = globalDefs;
        this.id = id;
        this.toBeSaved = toBeSaved;
    }

    @Override
    public FunctionalOperationContract map(UnaryOperator<Term> op, Services services) {
        Term newPres = op.apply(originalPre);
        Term newMby = op.apply(originalMby);
        Term newPost = op.apply(originalPost);
        Term newModifiable = op.apply(originalModifiable);
        Term newGlobalDefs = op.apply(globalDefs);

        return new FunctionalOperationContractImpl(baseName, name, krt, fn,
            modalityKind,
            newPres, newMby, newPost, newModifiable,
            originalParamVars, originalResultVar, newGlobalDefs,
            id, toBeSaved, services);
    }

    @Override
    public int id() {
        return id;
    }

    @Override
    public ProgramFunction getTarget() {
        return fn;
    }

    @Override
    public boolean hasMby() {
        return originalMby != null;
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public String getDisplayName() {
        return "";
    }

    @Override
    public boolean isPure() {
        return false;
    }

    @Override
    public Term getModifiable(ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars,
            Services services) {
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
        final Map<ProgramVariable, ProgramVariable> replaceMap =
            getReplaceMap(selfVar, paramVars, null, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalModifiable);
    }

    @Override
    public Modality.RustyModalityKind getModalityKind() {
        return modalityKind;
    }

    @Override
    public Term getEnsures() {
        return originalPost;
    }

    @Override
    public Term getPost(ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars,
            ProgramVariable resultVar, Services services) {
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
        final Map<ProgramVariable, ProgramVariable> replaceMap =
            getReplaceMap(selfVar, paramVars, resultVar, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(originalPost);
    }

    @Override
    public String getBaseName() {
        return "";
    }

    @Override
    public Term getPre() {
        return originalPre;
    }

    @Override
    public Term getPost() {
        return originalPost;
    }

    @Override
    public Term getModifiable() {
        return originalModifiable;
    }

    @Override
    public Term getMby() {
        return originalMby;
    }

    @Override
    public String getHTMLText(Services services) {
        return "";
    }

    @Override
    public String getPlainText(Services services) {
        return "";
    }

    @Override
    public boolean toBeSaved() {
        return toBeSaved;
    }

    @Override
    public Term getSelf() {
        // TODO
        return null;
    }

    @Override
    public ImmutableList<Term> getParams() {
        return tb.var(originalParamVars);
    }

    @Override
    public Term getResult() {
        return tb.var(originalResultVar);
    }

    /**
     * Get the according replace-map for the given variables.
     *
     * @param selfVar the self variable
     * @param paramVars the parameter variables
     * @param resultVar the result variable
     * @param services the services object
     * @return the replacement map
     */
    protected Map<ProgramVariable, ProgramVariable> getReplaceMap(ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
            Services services) {
        final Map<ProgramVariable, ProgramVariable> result = new LinkedHashMap<>();

        // self
        // if (selfVar != null) {
        // assertSubSort(selfVar, originalSelfVar);
        // result.put(originalSelfVar, selfVar);
        // }

        // parameters
        if (paramVars != null) {
            assert originalParamVars.size() == paramVars.size();
            final Iterator<ProgramVariable> it1 = originalParamVars.iterator();
            final Iterator<ProgramVariable> it2 = paramVars.iterator();
            while (it1.hasNext()) {
                ProgramVariable originalParamVar = it1.next();
                ProgramVariable paramVar = it2.next();
                // allow contravariant parameter types
                assertSubSort(originalParamVar, paramVar);
                result.put(originalParamVar, paramVar);
            }
        }

        // result
        if (resultVar != null) {
            // workaround to allow covariant return types (bug #1384)
            assertSubSort(resultVar, originalResultVar);
            result.put(originalResultVar, resultVar);
        }

        return result;
    }
}
