/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.*;

import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.speclang.Contract.OriginalVariables;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.util.InfFlowSpec;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

/**
 * Abstract base class for all default implementations of the sub-interfaces of
 * {@link AuxiliaryContract}.
 *
 * @author wacker, lanzinger
 */
public abstract class AbstractAuxiliaryContractImpl implements AuxiliaryContract {

    /**
     * @see #getBlock()
     */
    protected final StatementBlock block;

    /**
     * @see #getLabels()
     */
    protected final List<Label> labels;

    /**
     * @see #getMethod()
     */
    protected final IProgramMethod method;

    /**
     * @see AuxiliaryContract#getModalityKind()
     */
    protected final JModality.JavaModalityKind modalityKind;

    /**
     * @see #getInstantiationSelfTerm()
     */
    protected JTerm instantiationSelf;

    /**
     * @see #getPrecondition(LocationVariable, Services)
     */
    protected final Map<LocationVariable, JTerm> preconditions;

    /**
     * @see #getFreePrecondition(LocationVariable, Services)
     */
    protected final Map<LocationVariable, JTerm> freePreconditions;

    /**
     * @see #getMby()
     */
    protected final JTerm measuredBy;

    /**
     * @see #getPostcondition(LocationVariable, Services)
     */
    protected final Map<LocationVariable, JTerm> postconditions;

    /**
     * @see #getFreePostcondition(LocationVariable, Services)
     */
    protected final Map<LocationVariable, JTerm> freePostconditions;

    /**
     * @see #getModifiableClause(LocationVariable, Services)
     */
    protected final Map<LocationVariable, JTerm> modifiableClauses;

    /**
     * @see #getFreeModifiableClause(LocationVariable, Services)
     */
    protected final Map<LocationVariable, JTerm> freeModifiableClauses;

    /**
     * @see #getInfFlowSpecs()
     */
    protected ImmutableList<InfFlowSpec> infFlowSpecs;

    /**
     * @see #getVariables()
     */
    protected final Variables variables;

    /**
     * @see #isTransactionApplicable()
     */
    protected final boolean transactionApplicable;

    /**
     * @see #hasModifiableClause(LocationVariable)
     */
    protected final Map<LocationVariable, Boolean> hasModifiable;

    /**
     * @see #hasFreeModifiableClause(LocationVariable)
     */
    protected final Map<LocationVariable, Boolean> hasFreeModifiable;

    /**
     * @see #getBaseName()
     */
    protected final String baseName;

    /**
     * @see AuxiliaryContract#getFunctionalContracts()
     */
    private ImmutableSet<FunctionalAuxiliaryContract<?>> functionalContracts;

    /**
     *
     * @param baseName the base name.
     * @param block the block this contract belongs to.
     * @param labels all labels belonging to the block.
     * @param method the method containing the block.
     * @param modalityKind this contract's modality kind.
     * @param preconditions this contract's preconditions on every heap.
     * @param measuredBy this contract's measured-by term.
     * @param postconditions this contract's postconditions on every heap.
     * @param modifiableClauses this contract's modifiable clauses on every heap.
     * @param freeModifiableClauses this contract's free modifiable clauses on every heap.
     * @param infFlowSpecs this contract's information flow specifications.
     * @param variables this contract's variables.
     * @param transactionApplicable whether this contract is applicable for transactions.
     * @param hasModifiable a map specifying on which heaps this contract has a modifiable clause.
     * @param functionalContracts the functional contracts corresponding to this contract.
     */
    protected AbstractAuxiliaryContractImpl(final String baseName, final StatementBlock block,
            final List<Label> labels, final IProgramMethod method,
            final JModality.JavaModalityKind modalityKind,
            final Map<LocationVariable, JTerm> preconditions,
            final Map<LocationVariable, JTerm> freePreconditions, final JTerm measuredBy,
            final Map<LocationVariable, JTerm> postconditions,
            final Map<LocationVariable, JTerm> freePostconditions,
            final Map<LocationVariable, JTerm> modifiableClauses,
            final Map<LocationVariable, JTerm> freeModifiableClauses,
            final ImmutableList<InfFlowSpec> infFlowSpecs,
            final Variables variables,
            final boolean transactionApplicable,
            final Map<LocationVariable, Boolean> hasModifiable,
            final Map<LocationVariable, Boolean> hasFreeModifiable,
            ImmutableSet<FunctionalAuxiliaryContract<?>> functionalContracts) {
        assert block != null;
        assert labels != null;
        assert method != null;
        assert modalityKind != null;
        assert preconditions != null;
        assert postconditions != null;
        assert modifiableClauses != null;
        assert variables.breakFlags != null;
        assert variables.continueFlags != null;
        assert variables.exception != null;
        assert variables.remembranceHeaps != null && !variables.remembranceHeaps.isEmpty();
        assert variables.remembranceLocalVariables != null;
        this.baseName = baseName;
        this.block = block;
        this.labels = labels;
        this.method = method;
        this.modalityKind = modalityKind;
        this.preconditions = preconditions;
        this.freePreconditions = freePreconditions;
        this.measuredBy = measuredBy;
        this.postconditions = postconditions;
        this.freePostconditions = freePostconditions;
        this.modifiableClauses = modifiableClauses;
        this.freeModifiableClauses = freeModifiableClauses;
        this.infFlowSpecs = infFlowSpecs;
        this.variables = variables;
        this.transactionApplicable = transactionApplicable;
        this.hasModifiable = hasModifiable;
        this.hasFreeModifiable = hasFreeModifiable;
        this.functionalContracts = functionalContracts;
    }

    @Override
    public String getBaseName() {
        return baseName;
    }

    @Override
    public StatementBlock getBlock() {
        return block;
    }

    @Override
    public List<Label> getLabels() {
        return labels;
    }

    @Override
    public IProgramMethod getMethod() {
        return method;
    }

    @Override
    public KeYJavaType getKJT() {
        return method.getContainerType();
    }

    @Override
    public JModality.JavaModalityKind getModalityKind() {
        return modalityKind;
    }

    @Override
    public Variables getPlaceholderVariables() {
        return variables;
    }

    @Override
    public VisibilityModifier getVisibility() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isTransactionApplicable() {
        return transactionApplicable;
    }

    @Override
    public boolean isReadOnly(final Services services) {
        return modifiableClauses.get(services.getTypeConverter().getHeapLDT().getHeap())
                .op() == services.getTypeConverter().getLocSetLDT().getEmpty();
    }

    @Override
    public boolean hasModifiableClause(LocationVariable heap) {
        return hasModifiable.get(heap);
    }

    @Override
    public boolean hasFreeModifiableClause(LocationVariable heap) {
        return hasFreeModifiable.get(heap);
    }

    @Override
    public Variables getVariables() {
        return variables;
    }

    @Override
    public Terms getVariablesAsTerms(Services services) {
        JTerm selfTerm =
            (this.variables.self != null ? services.getTermBuilder().var(this.variables.self)
                    : null);
        return variables.termify(selfTerm);
    }

    /**
     * Replaces variables in a map of terms
     *
     * @param term a term.
     * @param variables replacements for {@link #getVariables()}
     * @param services services.
     * @return the term with every occurrence of a variable from {@link #getVariables()} replaced.
     */
    public JTerm getTerm(final JTerm term, final Variables variables, final Services services) {
        assert variables != null;
        assert (variables.self == null) == (this.variables.self == null);
        assert services != null;

        final OpReplacer replacer =
            new OpReplacer(createReplacementMap(variables, services), services.getTermFactory());
        return replacer.replace(term);
    }

    /**
     * Replaces variables in a map of terms
     *
     * @param term a term.
     * @param heap the replacement heap
     * @param terms replacements for {@link #getVariables()}
     * @param services services.
     * @return the term with every occurrence of a variable from {@link #getVariables()} replaced.
     */
    public JTerm getTerm(final JTerm term, final JTerm heap, final Terms terms,
            final Services services) {
        assert terms != null;
        assert (terms.self == null) == (this.variables.self == null);
        assert services != null;

        final OpReplacer replacer = new OpReplacer(createReplacementMap(heap, terms, services),
            services.getTermFactory(), services.getProof());
        return replacer.replace(term);
    }

    @Override
    public JTerm getMby() {
        return measuredBy;
    }

    @Override
    public JTerm getMby(Variables variables, Services services) {
        return getTerm(measuredBy, variables, services);
    }

    @Override
    public JTerm getMby(LocationVariable selfVar, Services services) {
        return getTerm(measuredBy,
            new Variables(selfVar, null, null, null, null, null, null, null, null, null, services),
            services);
    }

    @Override
    public JTerm getMby(Map<LocationVariable, JTerm> heapTerms, JTerm selfTerm,
            Map<LocationVariable, JTerm> atPres, Services services) {
        return getTerm(measuredBy, null,
            new Terms(selfTerm, null, null, null, null, null, null, null, null, atPres), services);
    }

    @Override
    public JTerm getPrecondition(final LocationVariable heap, final LocationVariable self,
            final Map<LocationVariable, LocationVariable> atPres, final Services services) {
        return getTerm(preconditions.get(heap),
            new Variables(self, null, null, null, null, null, null, null, null, atPres, services),
            services);
    }

    @Override
    public JTerm getPrecondition(final LocationVariable heapVariable, final JTerm heap,
            final JTerm self, final Map<LocationVariable, JTerm> atPres, final Services services) {
        return getTerm(preconditions.get(heapVariable), heap,
            new Terms(self, null, null, null, null, null, null, null, null, atPres), services);
    }

    @Override
    public JTerm getPrecondition(final LocationVariable heap, final Services services) {
        return getPrecondition(heap, variables.self, variables.outerRemembranceVariables, services);
    }

    @Override
    public JTerm getPrecondition(LocationVariable heap, Variables variables, Services services) {
        return getTerm(preconditions.get(heap), variables, services);
    }

    @Override
    public JTerm getPrecondition(LocationVariable heapVariable, JTerm heap, Terms terms,
            Services services) {
        return getTerm(preconditions.get(heapVariable), heap, terms, services);
    }

    @Override
    public JTerm getPostcondition(final LocationVariable heap, final Variables variables,
            final Services services) {
        return getTerm(postconditions.get(heap), variables, services);
    }

    @Override
    public JTerm getPostcondition(final LocationVariable heapVariable, final JTerm heap,
            final Terms terms, final Services services) {
        return getTerm(postconditions.get(heapVariable), heap, terms, services);
    }

    @Override
    public JTerm getPostcondition(final LocationVariable heap, final Services services) {
        return getPostcondition(heap, variables, services);
    }

    @Override
    public JTerm getFreePrecondition(final LocationVariable heap, final LocationVariable self,
            final Map<LocationVariable, LocationVariable> atPres, final Services services) {
        return getTerm(freePreconditions.get(heap),
            new Variables(self, null, null, null, null, null, null, null, null, atPres, services),
            services);
    }

    @Override
    public JTerm getFreePrecondition(final LocationVariable heapVariable, final JTerm heap,
            final JTerm self, final Map<LocationVariable, JTerm> atPres, final Services services) {
        return getTerm(freePreconditions.get(heapVariable), heap,
            new Terms(self, null, null, null, null, null, null, null, null, atPres), services);
    }

    @Override
    public JTerm getFreePrecondition(final LocationVariable heap, final Services services) {
        return getFreePrecondition(heap, variables.self, variables.outerRemembranceVariables,
            services);
    }

    @Override
    public JTerm getFreePrecondition(LocationVariable heap, Variables variables,
            Services services) {
        return getTerm(freePreconditions.get(heap), variables, services);
    }

    @Override
    public JTerm getFreePrecondition(LocationVariable heapVariable, JTerm heap, Terms terms,
            Services services) {
        return getTerm(freePreconditions.get(heapVariable), heap, terms, services);
    }

    @Override
    public JTerm getFreePostcondition(final LocationVariable heap, final Variables variables,
            final Services services) {
        return getTerm(freePostconditions.get(heap), variables, services);
    }

    @Override
    public JTerm getFreePostcondition(final LocationVariable heapVariable, final JTerm heap,
            final Terms terms, final Services services) {
        return getTerm(freePostconditions.get(heapVariable), heap, terms, services);
    }

    @Override
    public JTerm getFreePostcondition(final LocationVariable heap, final Services services) {
        return getFreePostcondition(heap, variables, services);
    }

    @Override
    public JTerm getModifiableClause(final LocationVariable heap, final LocationVariable self,
            final Services services) {
        return getTerm(modifiableClauses.get(heap),
            new Variables(self, null, null, null, null, null, null, null, null, null, services),
            services);
    }

    @Override
    public JTerm getModifiableClause(final LocationVariable heapVariable, final JTerm heap,
            final JTerm self, final Services services) {
        return getTerm(modifiableClauses.get(heapVariable), heap,
            new Terms(self, null, null, null, null, null, null, null, null, null), services);
    }

    @Override
    public JTerm getModifiableClause(final LocationVariable heap, final Variables variables,
            final Services services) {
        return getTerm(modifiableClauses.get(heap), variables, services);
    }

    @Override
    public JTerm getModifiableClause(final LocationVariable heap, final Services services) {
        return getModifiableClause(heap, variables.self, services);
    }

    @Override
    public JTerm getFreeModifiableClause(final LocationVariable heap, final LocationVariable self,
            final Services services) {
        return getTerm(
            freeModifiableClauses.get(heap),
            new Variables(self, null, null, null, null, null, null, null, null, null, services),
            services);
    }

    @Override
    public JTerm getFreeModifiableClause(final LocationVariable heapVariable, final JTerm heap,
            final JTerm self, final Services services) {
        return getTerm(
            freeModifiableClauses.get(heapVariable),
            heap,
            new Terms(self, null, null, null, null, null, null, null, null, null),
            services);
    }

    @Override
    public JTerm getFreeModifiableClause(
            final LocationVariable heap, final Variables variables, final Services services) {
        return getTerm(freeModifiableClauses.get(heap), variables, services);
    }

    @Override
    public JTerm getFreeModifiableClause(final LocationVariable heap, final Services services) {
        return getFreeModifiableClause(heap, variables.self, services);
    }

    @Override
    public JTerm getPre(Services services) {
        return preconditions.get(services.getTypeConverter().getHeapLDT().getHeap());
    }

    @Override
    public JTerm getFreePre(Services services) {
        return freePreconditions.get(services.getTypeConverter().getHeapLDT().getHeap());
    }

    @Override
    public JTerm getRequires(LocationVariable heap) {
        return preconditions.get(heap);
    }

    @Override
    public JTerm getRequiresFree(LocationVariable heap) {
        return freePreconditions.get(heap);
    }

    @Override
    public JTerm getPost(Services services) {
        return postconditions.get(services.getTypeConverter().getHeapLDT().getHeap());
    }

    @Override
    public JTerm getFreePost(Services services) {
        return freePostconditions.get(services.getTypeConverter().getHeapLDT().getHeap());
    }

    @Override
    public JTerm getEnsures(LocationVariable heap) {
        return postconditions.get(heap);
    }

    @Override
    public JTerm getEnsuresFree(LocationVariable heap) {
        return freePostconditions.get(heap);
    }

    @Override
    public JTerm getModifiable(Services services) {
        return modifiableClauses.get(services.getTypeConverter().getHeapLDT().getHeap());
    }

    @Override
    public ImmutableList<InfFlowSpec> getInfFlowSpecs() {
        return infFlowSpecs;
    }

    @Override
    public boolean hasMby() {
        return measuredBy != null;
    }

    @Override
    public boolean hasInfFlowSpecs() {
        return infFlowSpecs != null;
    }

    @Override
    public void setInstantiationSelf(JTerm selfInstantiation) {
        this.instantiationSelf = selfInstantiation;
    }

    @Override
    public JTerm getInstantiationSelfTerm() {
        return instantiationSelf;
    }

    @Override
    public JTerm getInstantiationSelfTerm(TermServices services) {
        if (instantiationSelf != null) {
            return instantiationSelf;
        } else if (variables.self != null) {
            return services.getTermBuilder().var(variables.self);
        } else {
            return null;
        }
    }

    @Override
    public IProgramMethod getTarget() {
        return method;
    }

    @Override
    public JTerm getModifiable(LocationVariable heap) {
        return modifiableClauses.get(heap);
    }

    @Override
    public String getHtmlText(final Services services) {
        assert services != null;
        // TODO Clean up.
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final LocationVariable baseHeap = heapLDT.getHeap();
        final StringBuilder stringBuilder = new StringBuilder();
        if (variables.result != null) {
            stringBuilder.append(variables.result);
            stringBuilder.append(" = ");
        } else if (method.isConstructor()) {
            stringBuilder.append(variables.self);
            stringBuilder.append(" = new ");
        }
        if (!method.isStatic() && !method.isConstructor()) {
            stringBuilder.append(variables.self);
            stringBuilder.append("#");
        }
        stringBuilder.append(method.getName());
        stringBuilder.append("()");
        stringBuilder.append(")");
        stringBuilder.append(" catch(");
        stringBuilder.append(variables.exception);
        stringBuilder.append(")");
        String modifiables = getHtmlModifiables(baseHeap, heapLDT, services);
        String pres = getHtmlPres(baseHeap, heapLDT, services);
        String posts = getHtmlPosts(baseHeap, heapLDT, services);
        return "<html>" + "<i>" + LogicPrinter.escapeHTML(stringBuilder.toString(), false) + "</i>"
            + pres + posts + modifiables + "<br><b>termination</b> " + getModalityKind()
            /*
             * + (transactionApplicableContract() ? "<br><b>transactionApplicable applicable</b>" :
             * "")
             */
            + "</html>";
    }

    @Override
    public String getPlainText(Services services) {
        return getPlainText(services, new Terms(variables, services.getTermBuilder()));
    }

    @Override
    public String getPlainText(final Services services, Terms terms) {
        assert services != null;
        // TODO Clean up.
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final LocationVariable baseHeap = heapLDT.getHeap();
        final StringBuilder stringBuilder = new StringBuilder();
        if (terms.result != null) {
            stringBuilder.append(terms.result);
            stringBuilder.append(" = ");
        } else if (method.isConstructor()) {
            stringBuilder.append(terms.self);
            stringBuilder.append(" = new ");
        }
        if (!method.isStatic() && !method.isConstructor()) {
            stringBuilder.append(terms.self);
            stringBuilder.append("#");
        }
        stringBuilder.append(method.getName());
        stringBuilder.append("()");
        stringBuilder.append(")");
        stringBuilder.append(" catch(");
        stringBuilder.append(terms.exception);
        stringBuilder.append(")");
        String modifiables = getPlainModifiables(terms.self, baseHeap, heapLDT, services);
        String pres = getPlainPres(terms, baseHeap, heapLDT, services);
        String posts = getPlainPosts(terms, baseHeap, heapLDT, services);
        return stringBuilder + pres + posts + modifiables + "termination " + getModalityKind();
    }

    @Override
    public OriginalVariables getOrigVars() {
        return variables.toOrigVars();
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        } else if (obj == null || getClass() != obj.getClass()) {
            return false;
        }
        AbstractAuxiliaryContractImpl other = (AbstractAuxiliaryContractImpl) obj;
        if ((block == null && other.block != null)
                || (block != null && !block.equals(other.block))) {
            return false;
        } else if ((hasModifiable == null && other.hasModifiable != null)
                || (hasModifiable != null && !hasModifiable.equals(other.hasModifiable))) {
            return false;
        } else if ((infFlowSpecs == null && other.infFlowSpecs != null)
                || (infFlowSpecs != null && !infFlowSpecs.equals(other.infFlowSpecs))) {
            return false;
        } else if ((instantiationSelf == null && other.instantiationSelf != null)
                || (instantiationSelf != null
                        && !instantiationSelf.equals(other.instantiationSelf))) {
            return false;
        } else if ((labels == null && other.labels != null)
                || (labels != null && !labels.equals(other.labels))) {
            return false;
        } else if ((method == null && other.method != null)
                || (method != null && !method.equals(other.method))) {
            return false;
        } else if ((modalityKind == null && other.modalityKind != null)
                || (modalityKind != null && !modalityKind.equals(other.modalityKind))) {
            return false;
        } else if ((modifiableClauses == null && other.modifiableClauses != null)
                || (modifiableClauses != null
                        && !modifiableClauses.equals(other.modifiableClauses))) {
            return false;
        } else if ((postconditions == null && other.postconditions != null)
                || (postconditions != null && !postconditions.equals(other.postconditions))) {
            return false;
        } else if ((preconditions == null && other.preconditions != null)
                || (preconditions != null && !preconditions.equals(other.preconditions))) {
            return false;
        } else if (transactionApplicable != other.transactionApplicable) {
            return false;
        } else {
            return (variables != null || other.variables == null)
                    && (variables == null || variables.equals(other.variables));
        }
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((block == null) ? 0 : block.hashCode());
        result = prime * result + ((hasModifiable == null) ? 0 : hasModifiable.hashCode());
        result = prime * result + ((infFlowSpecs == null) ? 0 : infFlowSpecs.hashCode());
        result = prime * result + ((instantiationSelf == null) ? 0 : instantiationSelf.hashCode());
        result = prime * result + ((labels == null) ? 0 : labels.hashCode());
        result = prime * result + ((method == null) ? 0 : method.hashCode());
        result = prime * result + ((modalityKind == null) ? 0 : modalityKind.hashCode());
        result = prime * result + ((modifiableClauses == null) ? 0 : modifiableClauses.hashCode());
        result = prime * result + ((postconditions == null) ? 0 : postconditions.hashCode());
        result = prime * result + ((preconditions == null) ? 0 : preconditions.hashCode());
        result = prime * result + (transactionApplicable ? 1231 : 1237);
        result = prime * result + ((variables == null) ? 0 : variables.hashCode());
        return result;
    }

    @Override
    public ImmutableSet<FunctionalAuxiliaryContract<?>> getFunctionalContracts() {
        return functionalContracts;
    }

    @Override
    public void setFunctionalContract(FunctionalAuxiliaryContract<?> contract) {
        assert contract.id() != Contract.INVALID_ID;
        functionalContracts =
            DefaultImmutableSet.<FunctionalAuxiliaryContract<?>>nil().add(contract);
    }

    /**
     *
     * @param newVariables new variables.
     * @param services services.
     * @return a map from every variable in {@link #getVariables()} to its counterpart in
     *         {@code newVariables}.
     */
    protected Map<LocationVariable, LocationVariable> createReplacementMap(
            final Variables newVariables, final Services services) {
        final VariableReplacementMap result = new VariableReplacementMap(services.getTermFactory());
        result.replaceSelf(variables.self, newVariables.self, services);
        result.replaceFlags(variables.breakFlags, newVariables.breakFlags, services);
        result.replaceFlags(variables.continueFlags, newVariables.continueFlags, services);
        result.replaceVariable(variables.returnFlag, newVariables.returnFlag, services);
        result.replaceVariable(variables.result, newVariables.result, services);
        result.replaceVariable(variables.exception, newVariables.exception, services);
        result.replaceRemembranceHeaps(variables.remembranceHeaps, newVariables.remembranceHeaps,
            services);
        result.replaceRemembranceLocalVariables(variables.remembranceLocalVariables,
            newVariables.remembranceLocalVariables, services);
        result.replaceRemembranceHeaps(variables.outerRemembranceHeaps,
            newVariables.outerRemembranceHeaps, services);
        result.replaceRemembranceLocalVariables(variables.outerRemembranceVariables,
            newVariables.outerRemembranceVariables, services);
        return result;
    }

    /**
     *
     * @param newHeap new base heap.
     * @param newTerms new terms.
     * @param services services.
     * @return a map from every term in {@code getVariables().termify()} to its counterpart in
     *         {@code newTerms}, and from the base heap to {@code heap}.
     */
    protected Map<JTerm, JTerm> createReplacementMap(final JTerm newHeap, final Terms newTerms,
            final Services services) {
        final TermReplacementMap result = new TermReplacementMap(services.getTermFactory());
        result.replaceHeap(newHeap, services);
        result.replaceSelf(variables.self, newTerms.self, services);
        result.replaceFlags(variables.breakFlags, newTerms.breakFlags, services);
        result.replaceFlags(variables.continueFlags, newTerms.continueFlags, services);
        result.replaceVariable(variables.returnFlag, newTerms.returnFlag, services);
        result.replaceVariable(variables.result, newTerms.result, services);
        result.replaceVariable(variables.exception, newTerms.exception, services);
        result.replaceRemembranceHeaps(variables.remembranceHeaps, newTerms.remembranceHeaps,
            services);
        result.replaceRemembranceLocalVariables(variables.remembranceLocalVariables,
            newTerms.remembranceLocalVariables, services);
        result.replaceRemembranceHeaps(variables.outerRemembranceHeaps,
            newTerms.outerRemembranceHeaps, services);
        result.replaceRemembranceLocalVariables(variables.outerRemembranceVariables,
            newTerms.outerRemembranceVariables, services);
        return result;
    }

    /**
     *
     * @param baseHeap base heap.
     * @param heapLDT heap LDT.
     * @param services services.
     * @return an HTML representation of this contract's modifiable clauses.
     */
    private String getHtmlModifiables(final LocationVariable baseHeap, final HeapLDT heapLDT,
            final Services services) {
        StringBuilder modifiables = new StringBuilder();
        for (LocationVariable heap : heapLDT.getAllHeaps()) {
            if (modifiableClauses.get(heap) != null) {
                modifiables.append("<br><b>modifiable")
                        .append(heap == baseHeap ? "" : "[" + heap + "]")
                        .append("</b> ").append(LogicPrinter.escapeHTML(
                            LogicPrinter.quickPrintTerm(modifiableClauses.get(heap), services),
                            false));
                /*
                 * if (heap == baseHeap && !hasRealModifiableClause) { modifiables = modifiables +
                 * "<b>, creates no new objects</b>"; }
                 */
            }
        }
        return modifiables.toString();
    }

    /**
     *
     * @param baseHeap base heap.
     * @param heapLDT heap LDT.
     * @param services services.
     * @return an HTML representation of this contract's preconditions.
     */
    private String getHtmlPres(final LocationVariable baseHeap, final HeapLDT heapLDT,
            final Services services) {
        StringBuilder pres = new StringBuilder();
        for (LocationVariable heap : heapLDT.getAllHeaps()) {
            if (preconditions.get(heap) != null) {
                pres.append("<br><b>pre").append(heap == baseHeap ? "" : "[" + heap + "]")
                        .append("</b> ").append(LogicPrinter.escapeHTML(
                            LogicPrinter.quickPrintTerm(preconditions.get(heap), services), false));
            }
        }
        return pres.toString();
    }

    /**
     *
     * @param baseHeap base heap.
     * @param heapLDT heap LDT.
     * @param services services.
     * @return an HTML representation of this contract's postconditions.
     */
    private String getHtmlPosts(final LocationVariable baseHeap, final HeapLDT heapLDT,
            final Services services) {
        StringBuilder posts = new StringBuilder();
        for (LocationVariable heap : heapLDT.getAllHeaps()) {
            if (postconditions.get(heap) != null) {
                posts.append("<br><b>post").append(heap == baseHeap ? "" : "[" + heap + "]")
                        .append("</b> ").append(LogicPrinter.escapeHTML(
                            LogicPrinter.quickPrintTerm(postconditions.get(heap), services),
                            false));
            }
        }
        return posts.toString();
    }

    /**
     *
     * @param self the self term
     * @param baseHeap base heap.
     * @param heapLDT heap LDT.
     * @param services services.
     * @return a plain text representation of this contract's modifiable clauses.
     */
    private String getPlainModifiables(JTerm self, final LocationVariable baseHeap,
            final HeapLDT heapLDT,
            final Services services) {
        StringBuilder modifiables = new StringBuilder();
        for (LocationVariable heap : heapLDT.getAllHeaps()) {
            JTerm modifiableClause =
                getModifiableClause(heap, services.getTermBuilder().var(heap), self, services);
            if (modifiableClause != null) {
                modifiables.append("\nmodifiable").append(heap == baseHeap ? "" : "[" + heap + "]")
                        .append(" ")
                        .append(LogicPrinter.quickPrintTerm(modifiableClause, services));
                /*
                 * if (heap == baseHeap && !hasRealModifiableClause) { modifiables = modifiables +
                 * "<b>, creates no new objects</b>"; }
                 */
            }
        }
        return modifiables.toString();
    }

    /**
     *
     * @param terms the terms to use.
     * @param baseHeap base heap.
     * @param heapLDT heap LDT.
     * @param services services.
     * @return a plain text representation of this contract's preconditions.
     */
    private String getPlainPres(Terms terms, final LocationVariable baseHeap, final HeapLDT heapLDT,
            final Services services) {
        StringBuilder pres = new StringBuilder();
        for (LocationVariable heap : heapLDT.getAllHeaps()) {
            JTerm precondition = getPrecondition(heap, services.getTermBuilder().var(baseHeap),
                terms.self, terms.remembranceHeaps, services);
            if (precondition != null) {
                pres.append("\npre").append(heap == baseHeap ? "" : "[" + heap + "]").append(" ")
                        .append(LogicPrinter.quickPrintTerm(precondition, services));
            }
        }
        return pres.toString();
    }

    /**
     *
     * @param terms the terms to use.
     * @param baseHeap base heap.
     * @param heapLDT heap LDT.
     * @param services services.
     * @return a plain text representation of this contract's postconditions.
     */
    private String getPlainPosts(Terms terms, final LocationVariable baseHeap,
            final HeapLDT heapLDT, final Services services) {
        StringBuilder posts = new StringBuilder();
        for (LocationVariable heap : heapLDT.getAllHeaps()) {
            JTerm postcondition =
                getPostcondition(heap, services.getTermBuilder().var(baseHeap), terms, services);
            if (postcondition != null) {
                posts.append("\npost").append(heap == baseHeap ? "" : "[" + heap + "]").append(" ")
                        .append(LogicPrinter.quickPrintTerm(postcondition, services));
            }
        }
        return posts.toString();
    }

    /**
     * This class contains a builder method for {@link AbstractAuxiliaryContractImpl}s
     * ({@link Creator#create()}). It should be overridden in every subclass.
     *
     * @param <T> the type of the subclass.
     */
    protected static abstract class Creator<T extends AuxiliaryContract> extends TermBuilder {

        /**
         * @see AuxiliaryContract#getBaseName()
         */
        private final String baseName;

        /**
         * @see AuxiliaryContract#getBlock()
         */
        private final StatementBlock block;

        /**
         * @see AuxiliaryContract#getLabels()
         */
        private final List<Label> labels;

        /**
         * @see AuxiliaryContract#getMethod()
         */
        private final IProgramMethod method;

        /**
         * This contract's behavior.
         */
        private final Behavior behavior;

        /**
         * @see AuxiliaryContract#getVariables()
         */
        private final Variables variables;

        /**
         * @see AuxiliaryContract#getMby()
         */
        private final JTerm measuredBy;

        /**
         * Precondition.
         */
        private final Map<LocationVariable, JTerm> requires;

        /**
         * Free precondition.
         */
        private final Map<LocationVariable, JTerm> requiresFree;

        /**
         * Postcondition for normal termination.
         */
        private final Map<LocationVariable, JTerm> ensures;

        /**
         * Free postcondition for normal termination.
         */
        private final Map<LocationVariable, JTerm> ensuresFree;

        /**
         * @see AuxiliaryContract#getInfFlowSpecs()
         */
        private final ImmutableList<InfFlowSpec> infFlowSpecs;

        /**
         * Postconditions for abrupt termination with {@code break} statements.
         */
        private final Map<Label, JTerm> breaks;

        /**
         * Postconditions for abrupt termination with {@code continue} statements.
         */
        private final Map<Label, JTerm> continues;

        /**
         * Postcondition for abrupt termination with {@code return} statements.
         */
        private final JTerm returns;

        /**
         * Postcondition for abrupt termination due to an uncaught exception.
         */
        private final JTerm signals;

        /**
         * A term specifying which uncaught exceptions may occur.
         */
        private final JTerm signalsOnly;

        /**
         * A diverges term.
         */
        private final JTerm diverges;

        /**
         * A map from every heap to an modifiable term.
         */
        private final Map<LocationVariable, JTerm> modifiables;

        /**
         * A map from every heap to a free modifiable term.
         */
        private final Map<LocationVariable, JTerm> modifiablesFree;

        /**
         * A list of heaps used in this contract.
         */
        private final ImmutableList<LocationVariable> heaps;

        /**
         * A map specifying on which heaps this contract has a modifiable clause.
         */
        private final Map<LocationVariable, Boolean> hasModifiable;

        /**
         * A map specifying on which heaps this contract has a free modifiable clause.
         */
        private final Map<LocationVariable, Boolean> hasFreeModifiable;

        /**
         *
         * @param baseName the contract's base name.
         * @param block the block the contract belongs to.
         * @param labels all labels belonging to the block.
         * @param method the method containing the block.
         * @param behavior the contract's behavior.
         * @param variables the variables.
         * @param requires the contract's precondition.
         * @param measuredBy the contract's measured-by clause.
         * @param ensures the contracts postcondition due to normal termination.
         * @param infFlowSpecs the contract's information flow specifications.
         * @param breaks the contract's postconditions for abrupt termination with {@code break}
         *        statements.
         * @param continues the contract's postconditions for abrupt termination with
         *        {@code continue} statements.
         * @param returns the contract's postcondition for abrupt termination with {@code return}
         *        statements.
         * @param signals the contract's postcondition for abrupt termination due to abrupt
         *        termination.
         * @param signalsOnly a term specifying which uncaught exceptions may occur.
         * @param diverges a diverges clause.
         * @param modifiables map from every heap to an modifiable term.
         * @param modifiablesFree map from every heap to a free modifiable term.
         * @param hasModifiable map specifying on which heaps this contract has a modifiable clause.
         * @param hasFreeModifiable map specifying on which heaps this contract has a free
         *        modifiable clause.
         * @param services services.
         */
        protected Creator(final String baseName, final StatementBlock block,
                final List<Label> labels,
                final IProgramMethod method, final Behavior behavior, final Variables variables,
                final Map<LocationVariable, JTerm> requires,
                final Map<LocationVariable, JTerm> requiresFree, final JTerm measuredBy,
                final Map<LocationVariable, JTerm> ensures,
                final Map<LocationVariable, JTerm> ensuresFree,
                final ImmutableList<InfFlowSpec> infFlowSpecs,
                final Map<Label, JTerm> breaks, final Map<Label, JTerm> continues,
                final JTerm returns,
                final JTerm signals, final JTerm signalsOnly, final JTerm diverges,
                final Map<LocationVariable, JTerm> modifiables,
                final Map<LocationVariable, JTerm> modifiablesFree,
                final Map<LocationVariable, Boolean> hasModifiable,
                final Map<LocationVariable, Boolean> hasFreeModifiable,
                final Services services) {
            super(services.getTermFactory(), services);
            this.baseName = baseName;
            this.block = block;
            this.labels = labels;
            this.method = method;
            this.behavior = behavior;
            this.variables = variables;
            this.requires = requires;
            this.requiresFree = requiresFree;
            this.measuredBy = measuredBy;
            this.ensures = ensures;
            this.ensuresFree = ensuresFree;
            this.infFlowSpecs = infFlowSpecs;
            this.breaks = breaks;
            this.continues = continues;
            this.returns = returns;
            this.signals = signals;
            this.signalsOnly = signalsOnly;
            this.diverges = diverges;
            this.modifiables = modifiables;
            this.modifiablesFree = modifiablesFree;
            this.heaps = services.getTypeConverter().getHeapLDT().getAllHeaps();
            this.hasModifiable = hasModifiable;
            this.hasFreeModifiable = hasFreeModifiable;
        }

        /**
         *
         * @return a new contract.
         */
        public ImmutableSet<T> create() {
            return create(buildPreconditions(), buildFreePreconditions(), buildPostconditions(),
                buildFreePostconditions(), buildModifiableClauses(), buildFreeModifiableClauses(),
                infFlowSpecs);
        }

        /**
         *
         * @return the contract's preconditions.
         */
        protected Map<LocationVariable, JTerm> buildPreconditions() {
            final Map<LocationVariable, JTerm> result = new LinkedHashMap<>();
            for (LocationVariable heap : heaps) {
                // Add JML precondition to precondition
                if (requires.get(heap) != null) {
                    result.put(heap, convertToFormula(requires.get(heap)));
                }

                // Add measured by term to precondition
                JTerm old = result.get(heap);
                JTerm mbyTerm;

                if (measuredBy != null && !measuredBy.equals(measuredByEmpty())) {
                    Map<JTerm, JTerm> replacementMap = new LinkedHashMap<>();

                    for (Map.Entry<LocationVariable, LocationVariable> remembranceVariable : variables.outerRemembranceVariables
                            .entrySet()) {
                        if (remembranceVariable.getValue() != null) {
                            replacementMap.put(var(remembranceVariable.getKey()),
                                var(remembranceVariable.getValue()));
                        }
                    }

                    for (Map.Entry<LocationVariable, LocationVariable> remembranceVariable : variables.outerRemembranceHeaps
                            .entrySet()) {
                        if (remembranceVariable.getValue() != null) {
                            replacementMap.put(var(remembranceVariable.getKey()),
                                var(remembranceVariable.getValue()));
                        }
                    }
                    mbyTerm = measuredBy(new OpReplacer(replacementMap, services.getTermFactory(),
                        services.getProof()).replace(measuredBy));
                } else {
                    mbyTerm = measuredByEmpty();
                }

                // InfFlow preconditions are without Mby term
                // (FIXME: a bit hacky for now, but works)
                if (old == null && (infFlowSpecs == null || infFlowSpecs.size() <= 0)) {
                    result.put(heap, mbyTerm);
                } else if (infFlowSpecs == null || infFlowSpecs.size() <= 0) {
                    result.put(heap, and(mbyTerm, old));
                }
            }
            return result;
        }

        /**
         *
         * @return the contract's free preconditions.
         */
        protected Map<LocationVariable, JTerm> buildFreePreconditions() {
            final Map<LocationVariable, JTerm> result = new LinkedHashMap<>();
            for (LocationVariable heap : heaps) {
                // Add JML precondition to precondition
                if (requiresFree.get(heap) != null) {
                    result.put(heap, convertToFormula(requiresFree.get(heap)));
                }
            }
            return result;
        }

        /**
         *
         * @return the contract's postconditions.
         */
        protected Map<LocationVariable, JTerm> buildPostconditions() {
            final Map<LocationVariable, JTerm> postconditions =
                new LinkedHashMap<>();
            for (LocationVariable heap : heaps) {
                if (ensures.get(heap) != null) {
                    postconditions.put(heap, buildPostcondition(heap));
                }
            }
            return postconditions;
        }

        /**
         *
         * @return the contract's postconditions.
         */
        protected Map<LocationVariable, JTerm> buildFreePostconditions() {
            final Map<LocationVariable, JTerm> freePostconditions =
                new LinkedHashMap<>();
            for (LocationVariable heap : heaps) {
                if (ensuresFree.get(heap) != null) {
                    freePostconditions.put(heap, buildFreePostcondition(heap));
                }
            }
            return freePostconditions;
        }

        /**
         *
         * @param heap the heap to use.
         * @return the contract's postcondition on the specified heap.
         */
        private JTerm buildPostcondition(final LocationVariable heap) {
            final JTerm breakPostcondition = conditionPostconditions(variables.breakFlags, breaks);
            final JTerm continuePostcondition =
                conditionPostconditions(variables.continueFlags, continues);
            final JTerm returnPostcondition = conditionPostcondition(variables.returnFlag, returns);
            final JTerm throwPostcondition = buildThrowPostcondition();
            // TODO Why do we handle the two cases differently?
            // Surely has something to do with transactions.
            if (heap == services.getTypeConverter().getHeapLDT().getHeap()) {
                if (behavior == Behavior.NORMAL_BEHAVIOR) {
                    return and(buildNormalTerminationCondition(),
                        convertToFormula(ensures.get(heap)));
                } else if (behavior == Behavior.BREAK_BEHAVIOR) {
                    return and(buildBreakTerminationCondition(), breakPostcondition);
                } else if (behavior == Behavior.CONTINUE_BEHAVIOR) {
                    return and(buildContinueTerminationCondition(), continuePostcondition);
                } else if (behavior == Behavior.RETURN_BEHAVIOR) {
                    return and(buildReturnTerminationCondition(), returnPostcondition);
                } else if (behavior == Behavior.EXCEPTIONAL_BEHAVIOR) {
                    return and(buildThrowTerminationCondition(), throwPostcondition);
                } else {
                    return and(
                        imp(buildNormalTerminationCondition(), convertToFormula(ensures.get(heap))),
                        breakPostcondition, continuePostcondition, returnPostcondition,
                        throwPostcondition);
                }
            } else {
                if (behavior == Behavior.NORMAL_BEHAVIOR) {
                    return and(buildNormalTerminationCondition(),
                        convertToFormula(ensures.get(heap)));
                } else {
                    return imp(buildNormalTerminationCondition(),
                        convertToFormula(ensures.get(heap)));
                }
            }
        }

        /**
         *
         * @param heap the heap to use.
         * @return the contract's free postcondition on the specified heap.
         */
        private JTerm buildFreePostcondition(final LocationVariable heap) {
            // TODO Why do we handle the two cases differently?
            // Surely has something to do with transactions.
            if (heap == services.getTypeConverter().getHeapLDT().getHeap()) {
                if (behavior == Behavior.NORMAL_BEHAVIOR) {
                    return convertToFormula(ensuresFree.get(heap));
                } else {
                    return tt();
                }
            } else {
                return convertToFormula(ensuresFree.get(heap));
            }
        }

        /**
         *
         * @param flags abrupt termination flags.
         * @param postconditions postconditions for abrupt termination.
         * @return a postcondition created conjunctively from the specified postconditions.
         */
        private JTerm conditionPostconditions(final Map<Label, LocationVariable> flags,
                final Map<Label, JTerm> postconditions) {
            JTerm result = tt();
            for (Label label : flags.keySet()) {
                result = and(result,
                    conditionPostcondition(flags.get(label), postconditions.get(label)));
            }
            return result;
        }

        /**
         *
         * @param flag an abrupt termination flag.
         * @param postcondition a postcondition for abrupt termination with the specified flag.
         * @return a part of the postcondition.
         */
        private JTerm conditionPostcondition(final ProgramVariable flag,
                final JTerm postcondition) {
            JTerm result = tt();
            if (flag != null) {
                result =
                    imp(equals(services.getTypeConverter().convertToLogicElement(flag), TRUE()),
                        postcondition == null ? tt() : postcondition);
            }
            return result;
        }

        /**
         *
         * @return the postcondition for abrupt termination due to an uncaught exception.
         */
        private JTerm buildThrowPostcondition() {
            return imp(not(equals(var(variables.exception), NULL())),
                and(convertToFormula(signals), convertToFormula(signalsOnly)));
        }

        /**
         *
         * @return a term corresponding to {@link Behavior#NORMAL_BEHAVIOR}
         */
        private JTerm buildNormalTerminationCondition() {
            return and(buildNormalTerminationCondition(variables.breakFlags),
                buildNormalTerminationCondition(variables.continueFlags),
                buildFlagIsCondition(variables.returnFlag, FALSE()),
                buildExceptionIsNullCondition());
        }

        /**
         *
         * @return a term corresponding to {@link Behavior#BREAK_BEHAVIOR}
         */
        private JTerm buildBreakTerminationCondition() {
            return and(buildAbruptTerminationCondition(variables.breakFlags),
                buildNormalTerminationCondition(variables.continueFlags),
                buildFlagIsCondition(variables.returnFlag, FALSE()),
                buildExceptionIsNullCondition());
        }

        /**
         *
         * @return a term corresponding to {@link Behavior#CONTINUE_BEHAVIOR}
         */
        private JTerm buildContinueTerminationCondition() {
            return and(buildNormalTerminationCondition(variables.breakFlags),
                buildAbruptTerminationCondition(variables.continueFlags),
                buildFlagIsCondition(variables.returnFlag, FALSE()),
                buildExceptionIsNullCondition());
        }

        /**
         *
         * @return a term corresponding to {@link Behavior#RETURN_BEHAVIOR}
         */
        private JTerm buildReturnTerminationCondition() {
            return and(buildNormalTerminationCondition(variables.breakFlags),
                buildNormalTerminationCondition(variables.continueFlags),
                buildFlagIsCondition(variables.returnFlag, TRUE()),
                buildExceptionIsNullCondition());
        }

        /**
         *
         * @return a term corresponding to {@link Behavior#EXCEPTIONAL_BEHAVIOR}
         */
        private JTerm buildThrowTerminationCondition() {
            return and(buildNormalTerminationCondition(variables.breakFlags),
                buildNormalTerminationCondition(variables.continueFlags),
                buildFlagIsCondition(variables.returnFlag, FALSE()),
                not(buildExceptionIsNullCondition()));
        }

        /**
         *
         * @param flags a map containing all abrupt termination flags.
         * @return a term corresponding to {@link Behavior#NORMAL_BEHAVIOR}
         */
        private JTerm buildNormalTerminationCondition(final Map<Label, LocationVariable> flags) {
            JTerm result = tt();
            for (Label label : flags.keySet()) {
                result = and(result, buildFlagIsCondition(flags.get(label), FALSE()));
            }
            return result;
        }

        /**
         *
         * @param flags a map containing all abrupt termination flags.
         * @return a term equivalent to the negation of {@link #buildNormalTerminationCondition()}
         */
        private JTerm buildAbruptTerminationCondition(final Map<Label, LocationVariable> flags) {
            JTerm result = ff();
            for (Label label : flags.keySet()) {
                result = or(result, buildFlagIsCondition(flags.get(label), TRUE()));
            }
            return result;
        }

        /**
         *
         * @param flag a boolean variable.
         * @param truth a boolean term.
         * @return a term which is true iff the flag is equal to the term.
         */
        private JTerm buildFlagIsCondition(final LocationVariable flag, final JTerm truth) {
            JTerm result = tt();
            if (flag != null) {
                result = equals(var(flag), truth);
            }
            return result;
        }

        /**
         *
         * @return a term which is true iff {@code variables.exception == null}.
         */
        private JTerm buildExceptionIsNullCondition() {
            return equals(var(variables.exception), NULL());
        }

        /**
         *
         * @return the contract's modifiable clauses.
         */
        private Map<LocationVariable, JTerm> buildModifiableClauses() {
            return modifiables;
        }

        /**
         *
         * @return the contract's free modifiable clauses.
         */
        private Map<LocationVariable, JTerm> buildFreeModifiableClauses() {
            return modifiablesFree;
        }

        /**
         *
         * @param preconditions the contracts' preconditions.
         * @param postconditions the contracts' postconditions.
         * @param modifiableClauses the contracts' modifiable clauses.
         * @param infFlowSpecs the contracts' information flow specifications.
         * @return a set of one or two contracts depending on whether the {@code diverges} clause
         *         is trivial (i.e., {@code true} or {@code false}) or not.
         */
        private ImmutableSet<T> create(final Map<LocationVariable, JTerm> preconditions,
                final Map<LocationVariable, JTerm> freePreconditions,
                final Map<LocationVariable, JTerm> postconditions,
                final Map<LocationVariable, JTerm> freePostconditions,
                final Map<LocationVariable, JTerm> modifiableClauses,
                final Map<LocationVariable, JTerm> freeModifiableClauses,
                final ImmutableList<InfFlowSpec> infFlowSpecs) {
            ImmutableSet<T> result = DefaultImmutableSet.nil();
            final boolean transactionApplicable = modifiableClauses
                    .get(services.getTypeConverter().getHeapLDT().getSavedHeap()) != null;
            result = result.add(build(baseName, block, labels, method,
                diverges.equals(ff()) ? JModality.JavaModalityKind.DIA
                        : JModality.JavaModalityKind.BOX,
                preconditions,
                freePreconditions, measuredBy, postconditions, freePostconditions,
                modifiableClauses, freeModifiableClauses,
                infFlowSpecs, variables, transactionApplicable, hasModifiable, hasFreeModifiable));
            if (divergesConditionCannotBeExpressedByAModality()) {
                result = result.add(build(baseName, block, labels, method,
                    JModality.JavaModalityKind.DIA,
                    addNegatedDivergesConditionToPreconditions(preconditions), freePreconditions,
                    measuredBy, postconditions, freePostconditions,
                    modifiableClauses, freeModifiableClauses,
                    infFlowSpecs, variables, transactionApplicable, hasModifiable,
                    hasFreeModifiable));
            }
            return result;
        }

        /**
         * @param baseName the base name.
         * @param block the block this contract belongs to.
         * @param labels all labels belonging to the block.
         * @param method the method containing the block.
         * @param modalityKind this contract's modality kind.
         * @param preconditions this contract's preconditions on every heap.
         * @param measuredBy this contract's measured-by term.
         * @param postconditions this contract's postconditions on every heap.
         * @param modifiableClauses this contract's modifiable clauses on every heap.
         * @param freeModifiableClauses this contract's free modifiable clauses on every heap.
         * @param infFlowSpecs this contract's information flow specifications.
         * @param variables this contract's variables.
         * @param transactionApplicable whether this contract is applicable for transactions.
         * @param hasModifiable a map specifying on which heaps this contract has a modifiable
         *        clause.
         * @param hasFreeModifiable a map specifying on which heaps this contract has a free
         *        modifiable clause.
         * @return an instance of {@code T} with the specified attributes.
         */
        protected abstract T build(String baseName, StatementBlock block, List<Label> labels,
                IProgramMethod method, JModality.JavaModalityKind modalityKind,
                Map<LocationVariable, JTerm> preconditions,
                Map<LocationVariable, JTerm> freePreconditions, JTerm measuredBy,
                Map<LocationVariable, JTerm> postconditions,
                Map<LocationVariable, JTerm> freePostconditions,
                Map<LocationVariable, JTerm> modifiableClauses,
                Map<LocationVariable, JTerm> freeModifiableClauses,
                ImmutableList<InfFlowSpec> infFlowSpecs, Variables variables,
                boolean transactionApplicable,
                Map<LocationVariable, Boolean> hasModifiable,
                Map<LocationVariable, Boolean> hasFreeModifiable);

        /**
         *
         * @return {@code true} iff the diverges condition can be expressed by a modality.
         */
        private boolean divergesConditionCannotBeExpressedByAModality() {
            return !diverges.equals(ff()) && !diverges.equals(tt());
        }

        /**
         *
         * @param preconditions a map containing the contract's preconditions.
         * @return a map with the negated diverges condition added to every precondition.
         */
        private Map<LocationVariable, JTerm> addNegatedDivergesConditionToPreconditions(
                final Map<LocationVariable, JTerm> preconditions) {
            final Map<LocationVariable, JTerm> result = new LinkedHashMap<>();
            for (LocationVariable heap : heaps) {
                if (preconditions.get(heap) != null) {
                    result.put(heap, and(preconditions.get(heap), not(convertToFormula(diverges))));
                }
            }
            return result;
        }

    }

    /**
     * This class is used to combine multiple contracts for the same block and apply them
     * simultaneously. It should be overridden in every subclass.
     *
     * @param <T> the type of the subclass.
     */
    protected static abstract class Combinator<T extends AuxiliaryContract> extends TermBuilder {

        /**
         * The contracts to combine.
         */
        protected final T[] contracts;

        /**
         * @see AuxiliaryContract#getPlaceholderVariables()
         */
        protected Variables placeholderVariables;

        /**
         * @see Variables#remembranceLocalVariables
         */
        protected Map<LocationVariable, LocationVariable> remembranceVariables;

        /**
         * @see AuxiliaryContract#getPrecondition(LocationVariable, Services)
         */
        protected final Map<LocationVariable, JTerm> preconditions;

        /**
         * @see AuxiliaryContract#getFreePrecondition(LocationVariable, Services)
         */
        protected final Map<LocationVariable, JTerm> freePreconditions;

        /**
         * @see AuxiliaryContract#getPostcondition(LocationVariable, Services)
         */
        protected final Map<LocationVariable, JTerm> postconditions;

        /**
         * @see AuxiliaryContract#getFreePrecondition(LocationVariable, Services)
         */
        protected final Map<LocationVariable, JTerm> freePostconditions;

        /**
         * @see AuxiliaryContract#getModifiableClause(LocationVariable, Services)
         */
        protected final Map<LocationVariable, JTerm> modifiableClauses;

        /**
         * @see AuxiliaryContract#getModifiableClause(LocationVariable, Services)
         */
        protected final Map<LocationVariable, JTerm> freeModifiableClauses;

        /**
         *
         * @param contracts the contracts to combine.
         * @param services services.
         */
        protected Combinator(final T[] contracts, final Services services) {
            super(services.getTermFactory(), services);
            this.contracts = sort(contracts);
            preconditions = new LinkedHashMap<>();
            freePreconditions = new LinkedHashMap<>();
            postconditions = new LinkedHashMap<>();
            freePostconditions = new LinkedHashMap<>();
            modifiableClauses = new LinkedHashMap<>();
            freeModifiableClauses = new LinkedHashMap<>();
        }

        /**
         *
         * @param contracts the contract's to sort.
         * @return an array containing the specified contracts sorted alphabetically by name.
         */
        private T[] sort(final T[] contracts) {
            // sort contracts alphabetically (for determinism)
            Arrays.sort(contracts, Comparator.comparing(SpecificationElement::getName));
            return contracts;
        }

        /**
         *
         * @return the combined contract.
         */
        protected abstract T combine();

        /**
         *
         * @param contract the contract whose conditions to add.
         */
        protected void addConditionsFrom(final T contract) {
            for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                final JTerm precondition = addPreconditionFrom(contract, heap);
                addFreePreconditionFrom(contract, heap);
                addPostconditionFrom(precondition, contract, heap);
                addFreePostconditionFrom(precondition, contract, heap);
                addModifiableClauseFrom(contract, heap);
                addFreeModifiableClauseFrom(contract, heap);
            }
        }

        /**
         *
         * @param contract the contract whose precondition to add.
         * @param heap the heap to use.
         * @return the precondition.
         */
        private JTerm addPreconditionFrom(final T contract, final LocationVariable heap) {
            final JTerm precondition = contract.getPrecondition(heap, placeholderVariables.self,
                placeholderVariables.remembranceHeaps, services);
            if (precondition != null) {
                preconditions.put(heap, orPossiblyNull(preconditions.get(heap), precondition));
            }
            return precondition;
        }

        /**
         *
         * @param contract the contract whose free precondition to add.
         * @param heap the heap to use.
         */
        private void addFreePreconditionFrom(final T contract, final LocationVariable heap) {
            final JTerm freePrecondition = contract.getFreePrecondition(heap,
                placeholderVariables.self, placeholderVariables.remembranceHeaps, services);
            if (freePrecondition != null) {
                freePreconditions.put(heap,
                    orPossiblyNull(freePreconditions.get(heap), freePrecondition));
            }
        }

        /**
         *
         * @param precondition the contract's precondition.
         * @param contract the contract the postcondition belongs to.
         * @param heap the heap to use.
         */
        private void addPostconditionFrom(final JTerm precondition, final T contract,
                final LocationVariable heap) {
            final JTerm unconditionalPostcondition =
                contract.getPostcondition(heap, placeholderVariables, services);
            if (unconditionalPostcondition != null) {
                final JTerm conditionalPostcondition =
                    imp(preify(precondition), unconditionalPostcondition);
                postconditions.put(heap,
                    andPossiblyNull(postconditions.get(heap), conditionalPostcondition));
            }
        }

        /**
         *
         * @param precondition the contract's precondition.
         * @param contract the contract the free postcondition belongs to.
         * @param heap the heap to use.
         */
        private void addFreePostconditionFrom(final JTerm precondition, final T contract,
                final LocationVariable heap) {
            final JTerm unconditionalFreePostcondition =
                contract.getFreePostcondition(heap, placeholderVariables, services);
            if (unconditionalFreePostcondition != null) {
                final JTerm conditionalFreePostcondition =
                    imp(preify(precondition), unconditionalFreePostcondition);
                freePostconditions.put(heap,
                    andPossiblyNull(freePostconditions.get(heap), conditionalFreePostcondition));
            }
        }

        /**
         *
         * @param contract the contract whose modifiable clause to add.
         * @param heap the heap to use.
         */
        private void addModifiableClauseFrom(final T contract, final LocationVariable heap) {
            final JTerm additionalModifiableClause =
                contract.getModifiableClause(heap, placeholderVariables.self, services);
            if (additionalModifiableClause != null) {
                modifiableClauses.put(heap,
                    unionPossiblyNull(modifiableClauses.get(heap), additionalModifiableClause));
            }
        }

        /**
         *
         * @param contract
         *        the contract whose modifiable clause to add.
         * @param heap
         *        the heap to use.
         */
        private void addFreeModifiableClauseFrom(final T contract, final LocationVariable heap) {
            final JTerm additionalModifiableClause =
                contract.getModifiableClause(heap, placeholderVariables.self, services);
            if (additionalModifiableClause != null) {
                freeModifiableClauses.put(heap,
                    unionPossiblyNull(freeModifiableClauses.get(heap), additionalModifiableClause));
            }
        }

        /**
         *
         * @param currentCondition a condition or {@code null}.
         * @param additionalCondition a condition.
         * @return the disjunction of the conditions.
         */
        private JTerm orPossiblyNull(final JTerm currentCondition,
                final JTerm additionalCondition) {
            if (currentCondition == null) {
                return additionalCondition;
            } else {
                return or(currentCondition, additionalCondition);
            }
        }

        /**
         *
         * @param currentCondition a condition or {@code null}.
         * @param additionalCondition a condition.
         * @return the conjunction of the conditions.
         */
        private JTerm andPossiblyNull(final JTerm currentCondition,
                final JTerm additionalCondition) {
            if (currentCondition == null) {
                return additionalCondition;
            } else {
                return and(currentCondition, additionalCondition);
            }
        }

        /**
         *
         * @param currentLocationSet a location set or {@code null}.
         * @param additionalLocationSet a location set.
         * @return the union of the location sets.
         */
        private JTerm unionPossiblyNull(final JTerm currentLocationSet,
                final JTerm additionalLocationSet) {
            if (currentLocationSet == null) {
                return additionalLocationSet;
            } else if (additionalLocationSet == null) {
                return currentLocationSet;
            } else {
                return union(currentLocationSet, additionalLocationSet);
            }
        }

        /**
         *
         * @param formula a formula.
         * @return the formula with all variables replaced by the remembrance variables.
         */
        private JTerm preify(final JTerm formula) {
            if (formula == null) {
                return tt();
            } else {
                final Map<JTerm, JTerm> replacementMap = new LinkedHashMap<>();

                for (Map.Entry<LocationVariable, LocationVariable> remembranceVariable : remembranceVariables
                        .entrySet()) {
                    if (remembranceVariable.getValue() != null) {
                        replacementMap.put(var(remembranceVariable.getKey()),
                            var(remembranceVariable.getValue()));
                    }
                }
                return new OpReplacer(replacementMap, services.getTermFactory(),
                    services.getProof()).replace(formula);
            }
        }

    }
}
