// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang;

import java.util.Arrays;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Sorted;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.rule.join.JoinProcedure;
import de.uka.ilkd.key.speclang.Contract.OriginalVariables;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.util.InfFlowSpec;

public final class SimpleBlockContract implements BlockContract {

    public static BlockContract combine(ImmutableSet<BlockContract> contracts, Services services) {
        return new Combinator(contracts, services).combine();
    }

    private final StatementBlock block;
    private final List<Label> labels;
    private final IProgramMethod method;
    private final Modality modality;
    private Term instantiationSelf;

    private final Map<LocationVariable, Term> preconditions;
    private final Map<LocationVariable, Term> postconditions;
    private final Map<LocationVariable, Term> modifiesClauses;
    private ImmutableList<InfFlowSpec> infFlowSpecs;
    private JoinProcedure joinProcedure;


    private final Variables variables;

    private final boolean transactionApplicable;
    
    private final Map<LocationVariable,Boolean> hasMod;

    public SimpleBlockContract(final StatementBlock block,
                               final List<Label> labels,
                               final IProgramMethod method,
                               final Modality modality,
                               final Map<LocationVariable, Term> preconditions,
                               final Map<LocationVariable, Term> postconditions,
                               final Map<LocationVariable, Term> modifiesClauses,
                               final ImmutableList<InfFlowSpec> infFlowSpecs,
                               final JoinProcedure joinProcedure,
                               final Variables variables,
                               final boolean transactionApplicable,
                               final Map<LocationVariable,Boolean> hasMod)
    {
        assert block != null;
        assert labels != null;
        assert method != null;
        assert modality != null;
        assert preconditions != null;
        assert postconditions != null;
        assert modifiesClauses != null;
        assert variables.breakFlags != null;
        assert variables.continueFlags != null;
        assert variables.exception != null;
        assert variables.remembranceHeaps != null && variables.remembranceHeaps.size() > 0;
        assert variables.remembranceLocalVariables != null;
        this.block = block;
        this.labels = labels;
        this.method = method;
        this.modality = modality;
        this.preconditions = preconditions;
        this.postconditions = postconditions;
        this.modifiesClauses = modifiesClauses;        
        this.infFlowSpecs = infFlowSpecs;
        this.joinProcedure = joinProcedure;
        this.variables = variables;
        this.transactionApplicable = transactionApplicable;
        this.hasMod = hasMod;
    }

    @Override
    public StatementBlock getBlock()
    {
        return block;
    }

    @Override
    public List<Label> getLabels()
    {
        return labels;
    }

    @Override
    public IProgramMethod getMethod()
    {
        return method;
    }

    @Override
    public KeYJavaType getKJT()
    {
        return method.getContainerType();
    }

    @Override
    public Modality getModality()
    {
        return modality;
    }

    @Override
    public Variables getPlaceholderVariables()
    {
        return variables;
    }

    @Override
    public boolean isTransactionApplicable()
    {
        return transactionApplicable;
    }

    @Override
    public boolean isReadOnly(final Services services)
    {
        return modifiesClauses.get(services.getTypeConverter().getHeapLDT().getHeap()).op()
                == services.getTypeConverter().getLocSetLDT().getEmpty();
    }

    
    @Override
    public boolean hasModifiesClause(LocationVariable heap) {
        return hasMod.get(heap);
    }


    @Override
    public Variables getVariables() {
        return variables;
    }


    @Override
    public Terms getVariablesAsTerms(Services services) {
        Term selfTerm = (this.variables.self != null ?
                         services.getTermBuilder().var(this.variables.self) :
                         null);
        return variables.termify(selfTerm);
    }


    @Override
    public Term getPrecondition(final LocationVariable heap,
                                final ProgramVariable self,
                                final Map<LocationVariable, LocationVariable> remembranceHeaps,
                                final Services services)
    {
        assert heap != null;
        assert (self == null) == (variables.self == null);
        assert remembranceHeaps != null;
        assert services != null;
        final Map<ProgramVariable, ProgramVariable> replacementMap = createReplacementMap(
            new Variables(self, null, null, null, null, null, remembranceHeaps, null, services), services
        );
        final OpReplacer replacer = new OpReplacer(replacementMap, services.getTermFactory());
        return replacer.replace(preconditions.get(heap));
    }

    @Override
    public Term getPrecondition(final LocationVariable heapVariable,
                                final Term heap,
                                final Term self,
                                final Map<LocationVariable, Term> remembranceHeaps,
                                final Services services)
    {
        assert heapVariable != null;
        assert heap != null;
        assert (self == null) == (variables.self == null);
        assert remembranceHeaps != null;
        assert services != null;
        final Map<Term, Term> replacementMap = createReplacementMap(
            heap, new Terms(self, null, null, null, null, null, remembranceHeaps, null), services
        );
        final OpReplacer replacer = new OpReplacer(replacementMap, services.getTermFactory());
        return replacer.replace(preconditions.get(heapVariable));
    }

    @Override
    public Term getPrecondition(final LocationVariable heap, final Services services)
    {
        return getPrecondition(heap, variables.self, variables.remembranceHeaps, services);
    }

    @Override
    public Term getPostcondition(final LocationVariable heap,
                                 final Variables variables,
                                 final Services services) {
        assert heap != null;
        assert variables != null;
        assert (variables.self == null) == (this.variables.self == null);
        assert services != null;
        final OpReplacer replacer = new OpReplacer(createReplacementMap(variables, services), 
                                                   services.getTermFactory());
        return replacer.replace(postconditions.get(heap));
    }

    @Override
    public Term getPostcondition(final LocationVariable heapVariable, final Term heap,
                                 final Terms terms, final Services services) {
        assert heapVariable != null;
        assert heap != null;
        assert terms != null;
        assert (terms.self == null) == (variables.self == null);
        assert services != null;
        final OpReplacer replacer = new OpReplacer(createReplacementMap(heap, terms, services), 
                                                   services.getTermFactory());
        return replacer.replace(postconditions.get(heapVariable));
    }

    @Override
    public Term getPostcondition(final LocationVariable heap, final Services services)
    {
        return getPostcondition(heap, variables, services);
    }

    @Override
    public Term getModifiesClause(final LocationVariable heap,
                                  final ProgramVariable self,
                                  final Services services) {
        assert heap != null;
        assert (self == null) == (variables.self == null);
        assert services != null;
        final Map<ProgramVariable, ProgramVariable> replacementMap =
                createReplacementMap(new Variables(self, null, null, null, null,
                                                   null, null, null, services),
                                     services);
        final OpReplacer replacer = new OpReplacer(replacementMap, services.getTermFactory());
        return replacer.replace(modifiesClauses.get(heap));
    }

    @Override
    public Term getModifiesClause(final LocationVariable heapVariable, final Term heap,
                                  final Term self, final Services services) {
        assert heapVariable != null;
        assert heap != null;
        assert (self == null) == (variables.self == null);
        assert services != null;
        final Map<Term, Term> replacementMap = createReplacementMap(
            heap, new Terms(self, null, null, null, null, null, null, null), services
        );
        final OpReplacer replacer = new OpReplacer(replacementMap, services.getTermFactory());
        return replacer.replace(modifiesClauses.get(heapVariable));
    }

    @Override
    public Term getModifiesClause(final LocationVariable heap, final Services services)
    {
        return getModifiesClause(heap, variables.self, services);
    }


    @Override
    public Term getPre(Services services) {
        return preconditions.get(services.getTypeConverter().getHeapLDT().getHeap());
    }

    public Term getRequires(LocationVariable heap) {
        return preconditions.get(heap);
    }


    @Override
    public Term getPost(Services services) {
        return postconditions.get(services.getTypeConverter().getHeapLDT().getHeap());
    }

    public Term getEnsures(LocationVariable heap) {
        return postconditions.get(heap);
    }


    @Override
    public Term getMod(Services services) {
        return modifiesClauses.get(services.getTypeConverter().getHeapLDT().getHeap());
    }


    @Override
    public ImmutableList<InfFlowSpec> getInfFlowSpecs() {
        return infFlowSpecs;
    }


    public Term getAssignable(LocationVariable heap) {
        return modifiesClauses.get(heap);
    }
    
    public JoinProcedure getJoinProcedure() {
        return joinProcedure;
    }

    @Override
    public void visit(final Visitor visitor)
    {
        assert visitor != null;
        visitor.performActionOnBlockContract(this);
    }

    @Override
    public String getName() {
        return "Block Contract";
    }

    @Override
    public String getUniqueName() {
        if (getTarget() != null)
            return "Block Contract " + getBlock().getStartPosition().getLine() +
                    " " + getTarget().getUniqueName();
        else
            return "Block Contract " + getBlock().getStartPosition().getLine() +
                    " " + Math.abs(getBlock().hashCode());
    }

    @Override
    public String getDisplayName() {
        return "Block Contract";
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
        }
        else if (method.isConstructor()) {
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
        String mods = "";
        for (LocationVariable heap : heapLDT.getAllHeaps()) {
            if (modifiesClauses.get(heap) != null) {
                mods = mods + "<br><b>mod" + (heap == baseHeap ? "" : "[" + heap + "]") + "</b> "
                        + LogicPrinter.escapeHTML(
                                LogicPrinter.quickPrintTerm(modifiesClauses.get(heap), services),
                                false);
                /*if (heap == baseHeap && !hasRealModifiesClause) {
                    mods = mods + "<b>, creates no new objects</b>";
                }*/
            }
        }
        String pres = "";
        for (LocationVariable heap : heapLDT.getAllHeaps()) {
            if (preconditions.get(heap) != null) {
                pres = pres + "<br><b>pre" + (heap == baseHeap ? "" : "[" + heap + "]") + "</b> "
                        + LogicPrinter.escapeHTML(
                                LogicPrinter.quickPrintTerm(preconditions.get(heap), services),
                                false);
            }
        }
        String posts = "";
        for (LocationVariable heap : heapLDT.getAllHeaps()) {
            if (postconditions.get(heap) != null) {
                posts = posts + "<br><b>post" + (heap == baseHeap ? "" : "[" + heap + "]") + "</b> "
                         + LogicPrinter.escapeHTML(
                                 LogicPrinter.quickPrintTerm(postconditions.get(heap), services),
                                 false);
            }
        }
        return "<html>"
                + "<i>" + LogicPrinter.escapeHTML(stringBuilder.toString(), false) + "</i>"
                + pres
                + posts
                + mods
                + "<br><b>termination</b> "
                + getModality()
                /*+ (transactionApplicableContract() ? "<br><b>transactionApplicable applicable</b>" : "")*/
                + "</html>";
    }

    @Override
    public VisibilityModifier getVisibility()
    {
        assert false;
        return null;
    }

    @Override
    public BlockContract update(final StatementBlock newBlock,
                                final Map<LocationVariable,Term> newPreconditions,
                                final Map<LocationVariable,Term> newPostconditions,
                                final Map<LocationVariable,Term> newModifiesClauses,
                                final ImmutableList<InfFlowSpec> newinfFlowSpecs,
                                final JoinProcedure newJoinProcedure,
                                final Variables newVariables) {
        return new SimpleBlockContract(newBlock, labels, method, modality,
                                       newPreconditions, newPostconditions,
                                       newModifiesClauses, newinfFlowSpecs,
                                       newJoinProcedure,
                                       newVariables, transactionApplicable,
                                       hasMod);
    }

    @Override 
    public BlockContract setBlock(StatementBlock newBlock) {
        return update(newBlock, preconditions, postconditions, modifiesClauses,
                      infFlowSpecs, joinProcedure, variables);
    }

    public BlockContract setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        assert newPM instanceof IProgramMethod;
        assert newKJT.equals(newPM.getContainerType());
        return new SimpleBlockContract(block, labels, (IProgramMethod)newPM, modality,
                                       preconditions, postconditions, modifiesClauses,
                                       infFlowSpecs, joinProcedure, variables, transactionApplicable,
                                       hasMod);
    }

    public OriginalVariables getOrigVars() {
        Map<LocationVariable, ProgramVariable> atPreVars =
                new LinkedHashMap<LocationVariable, ProgramVariable>();
        for (LocationVariable h: variables.remembranceLocalVariables.keySet()) {
            atPreVars.put(h, variables.remembranceLocalVariables.get(h));
        }
        return new OriginalVariables(variables.self, variables.result,
                                     variables.exception, atPreVars,
                                     ImmutableSLList.<ProgramVariable>nil());
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        SimpleBlockContract other = (SimpleBlockContract) obj;
        if (block == null) {
            if (other.block != null)
                return false;
        }
        else if (!block.equals(other.block))
            return false;
        if (hasMod == null) {
            if (other.hasMod != null)
                return false;
        }
        else if (!hasMod.equals(other.hasMod))
            return false;
        if (infFlowSpecs == null) {
            if (other.infFlowSpecs != null)
                return false;
        }
        else if (!infFlowSpecs.equals(other.infFlowSpecs))
            return false;
        if (instantiationSelf == null) {
            if (other.instantiationSelf != null)
                return false;
        }
        else if (!instantiationSelf.equals(other.instantiationSelf))
            return false;
        if (joinProcedure == null) {
            if (other.joinProcedure != null)
                return false;
        }
        else if (!joinProcedure.equals(other.joinProcedure))
            return false;
        if (labels == null) {
            if (other.labels != null)
                return false;
        }
        else if (!labels.equals(other.labels))
            return false;
        if (method == null) {
            if (other.method != null)
                return false;
        }
        else if (!method.equals(other.method))
            return false;
        if (modality == null) {
            if (other.modality != null)
                return false;
        }
        else if (!modality.equals(other.modality))
            return false;
        if (modifiesClauses == null) {
            if (other.modifiesClauses != null)
                return false;
        }
        else if (!modifiesClauses.equals(other.modifiesClauses))
            return false;
        if (postconditions == null) {
            if (other.postconditions != null)
                return false;
        }
        else if (!postconditions.equals(other.postconditions))
            return false;
        if (preconditions == null) {
            if (other.preconditions != null)
                return false;
        }
        else if (!preconditions.equals(other.preconditions))
            return false;
        if (transactionApplicable != other.transactionApplicable)
            return false;
        if (variables == null) {
            if (other.variables != null)
                return false;
        }
        else if (!variables.equals(other.variables))
            return false;
        return true;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((block == null) ? 0 : block.hashCode());
        result = prime * result + ((hasMod == null) ? 0 : hasMod.hashCode());
        result = prime * result
                + ((infFlowSpecs == null) ? 0 : infFlowSpecs.hashCode());
        result = prime
                * result
                + ((instantiationSelf == null) ? 0 : instantiationSelf
                        .hashCode());
        result = prime * result
                + ((joinProcedure == null) ? 0 : joinProcedure.hashCode());
        result = prime * result + ((labels == null) ? 0 : labels.hashCode());
        result = prime * result + ((method == null) ? 0 : method.hashCode());
        result = prime * result
                + ((modality == null) ? 0 : modality.hashCode());
        result = prime * result
                + ((modifiesClauses == null) ? 0 : modifiesClauses.hashCode());
        result = prime * result
                + ((postconditions == null) ? 0 : postconditions.hashCode());
        result = prime * result
                + ((preconditions == null) ? 0 : preconditions.hashCode());
        result = prime * result + (transactionApplicable ? 1231 : 1237);
        result = prime * result
                + ((variables == null) ? 0 : variables.hashCode());
        return result;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return "SimpleBlockContract [block=" + block + ", labels=" + labels
                + ", method=" + method + ", modality=" + modality
                + ", instantiationSelf=" + instantiationSelf
                + ", preconditions=" + preconditions + ", postconditions="
                + postconditions + ", modifiesClauses=" + modifiesClauses
                + ", infFlowSpecs=" + infFlowSpecs + ", joinProcedure="
                + joinProcedure + ", variables=" + variables
                + ", transactionApplicable=" + transactionApplicable
                + ", hasMod=" + hasMod + "]";
    }

    private Map<ProgramVariable, ProgramVariable>
                createReplacementMap(final Variables newVariables,
                                     final Services services) {
        final VariableReplacementMap result = new VariableReplacementMap();
        result.replaceSelf(variables.self, newVariables.self, services);
        result.replaceFlags(variables.breakFlags, newVariables.breakFlags, services);
        result.replaceFlags(variables.continueFlags, newVariables.continueFlags, services);
        result.replaceVariable(variables.returnFlag, newVariables.returnFlag, services);
        result.replaceVariable(variables.result, newVariables.result, services);
        result.replaceVariable(variables.exception, newVariables.exception, services);
        result.replaceRemembranceHeaps(variables.remembranceHeaps,
                                       newVariables.remembranceHeaps,
                                       services);
        result.replaceRemembranceLocalVariables(variables.remembranceLocalVariables,
                                                newVariables.remembranceLocalVariables,
                                                services);
        return result;
    }

    private Map<Term, Term> createReplacementMap(final Term newHeap,
                                                 final Terms newTerms,
                                                 final Services services) {
        final TermReplacementMap result = new TermReplacementMap();
        result.replaceHeap(newHeap, services);
        result.replaceSelf(variables.self, newTerms.self, services);
        result.replaceFlags(variables.breakFlags, newTerms.breakFlags, services);
        result.replaceFlags(variables.continueFlags, newTerms.continueFlags, services);
        result.replaceVariable(variables.returnFlag, newTerms.returnFlag, services);
        result.replaceVariable(variables.result, newTerms.result, services);
        result.replaceVariable(variables.exception, newTerms.exception, services);
        result.replaceRemembranceHeaps(variables.remembranceHeaps,
                                       newTerms.remembranceHeaps,
                                       services);
        result.replaceRemembranceLocalVariables(variables.remembranceLocalVariables,
                                                newTerms.remembranceLocalVariables,
                                                services);
        return result;
    }


    @Override
    public boolean hasMby() {
        return false;
    }

    @Override
    public boolean hasInfFlowSpecs() {
        return infFlowSpecs != null;
    }

    @Override
    public boolean hasJoinProcedure() {
        return joinProcedure != null;
    }

    @Override
    public void setInstantiationSelf(Term selfInstantiation) {
        this.instantiationSelf = selfInstantiation;
    }

    @Override
    public Term getInstantiationSelfTerm(TermServices services) {
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


    private abstract static class ReplacementMap<S extends Sorted> extends LinkedHashMap<S, S> {

        private static final long serialVersionUID = -2339350643000987576L;

        public void replaceSelf(final ProgramVariable oldSelf, final S newSelf, TermServices services)
        {
            if (newSelf != null) {
                assert newSelf.sort().extendsTrans(oldSelf.sort());
                put(convert(oldSelf, services), newSelf);
            }
        }

        public void replaceFlags(final Map<Label, ProgramVariable> oldFlags,
                                 final Map<Label, S> newFlags,
                                 TermServices services) {
            if (newFlags != null) {
                assert newFlags.size() == oldFlags.size();
                for (Map.Entry<Label, ProgramVariable> oldFlag : oldFlags.entrySet()) {
                    replaceVariable(oldFlag.getValue(), newFlags.get(oldFlag.getKey()), services);
                }
            }
        }

        public void replaceVariable(final ProgramVariable oldVariable, final S newVariable, TermServices services)
        {
            if (newVariable != null) {
                assert oldVariable.sort().equals(newVariable.sort());
                put(convert(oldVariable, services), newVariable);
            }
        }

        public void replaceRemembranceHeaps(final Map<LocationVariable,
                                                      LocationVariable> oldRemembranceHeaps,
                                            final Map<LocationVariable,
                                                      ? extends S> newRemembranceHeaps,
                                            final Services services) {
            if (newRemembranceHeaps != null) {
                for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                    if (newRemembranceHeaps.get(heap) != null) {
                        final LocationVariable oldRemembranceHeap = oldRemembranceHeaps.get(heap);
                        final S newRemembranceHeap = newRemembranceHeaps.get(heap);
                        assert oldRemembranceHeap.sort().equals(newRemembranceHeap.sort());
                        put(convert(oldRemembranceHeap, services), newRemembranceHeap);
                    }
                }
            }
        }

        public void replaceRemembranceLocalVariables(final Map<LocationVariable, LocationVariable>
                                                                      oldRemembranceLocalVariables,
                                                     final Map<LocationVariable, ? extends S>
                                                                      newRemembranceLocalVariables, 
                                                     final TermServices services)
        {
            if (newRemembranceLocalVariables != null) {
                for (LocationVariable localVariable : oldRemembranceLocalVariables.keySet()) {
                    if (newRemembranceLocalVariables.get(localVariable) != null) {
                        LocationVariable oldRemembranceLocalVariable =
                                oldRemembranceLocalVariables.get(localVariable);
                        S newRemembranceLocalVariable =
                                newRemembranceLocalVariables.get(localVariable);
                        assert oldRemembranceLocalVariable.sort().equals(
                                newRemembranceLocalVariable.sort());
                        put(convert(oldRemembranceLocalVariable, services), newRemembranceLocalVariable);
                    }
                }
            }
        }

        protected abstract S convert(ProgramVariable variable, TermServices services);

    }

    private static class VariableReplacementMap extends ReplacementMap<ProgramVariable> {

        private static final long serialVersionUID = 8964634070766482218L;

        protected ProgramVariable convert(ProgramVariable variable, TermServices services)
        {
            return variable;
        }

    }

    private static class TermReplacementMap extends ReplacementMap<Term> {

        private static final long serialVersionUID = 5465241780257247301L;

        public void replaceHeap(final Term newHeap, final Services services)
        {
            assert newHeap != null;
            assert newHeap.sort().equals(services.getTypeConverter().getHeapLDT().targetSort());
            put(services.getTermBuilder().getBaseHeap(), newHeap);
        }

        @Override
        protected Term convert(ProgramVariable variable, TermServices services)
        {
            return services.getTermBuilder().var(variable);
        }

    }

    public static final class Creator extends TermBuilder {

        private final StatementBlock block;
        private final List<Label> labels;
        private final IProgramMethod method;
        private final Behavior behavior;
        private final Variables variables;
        private final Map<LocationVariable, Term> requires;
        private final Map<LocationVariable, Term> ensures;
        private final ImmutableList<InfFlowSpec> infFlowSpecs;
        private final JoinProcedure joinProcedure;
        private final Map<Label, Term> breaks;
        private final Map<Label, Term> continues;
        private final Term returns;
        private final Term signals;
        private final Term signalsOnly;
        private final Term diverges;
        private final Map<LocationVariable, Term> assignables;
        private final ImmutableList<LocationVariable> heaps;
        private final Map<LocationVariable,Boolean> hasMod;

        public Creator(final StatementBlock block,
                       final List<Label> labels,
                       final IProgramMethod method,
                       final Behavior behavior,
                       final Variables variables,
                       final Map<LocationVariable, Term> requires,
                       final Map<LocationVariable, Term> ensures,
                       final ImmutableList<InfFlowSpec> infFlowSpecs,
                       final JoinProcedure joinProcedure,
                       final Map<Label, Term> breaks,
                       final Map<Label, Term> continues,
                       final Term returns,
                       final Term signals,
                       final Term signalsOnly,
                       final Term diverges,
                       final Map<LocationVariable, Term> assignables,
                       final Map<LocationVariable,Boolean> hasMod,
                       final Services services) {
            super(services.getTermFactory(), services);
            this.block = block;
            this.labels = labels;
            this.method = method;
            this.behavior = behavior;
            this.variables = variables;
            this.requires = requires;
            this.ensures = ensures;
            this.infFlowSpecs = infFlowSpecs;
            this.joinProcedure = joinProcedure;
            this.breaks = breaks;
            this.continues = continues;
            this.returns = returns;
            this.signals = signals;
            this.signalsOnly = signalsOnly;
            this.diverges = diverges;
            this.assignables = assignables;
            this.heaps = services.getTypeConverter().getHeapLDT().getAllHeaps();
            this.hasMod = hasMod;
        }

        public ImmutableSet<BlockContract> create() {
            return create(buildPreconditions(), buildPostconditions(),
                          buildModifiesClauses(), infFlowSpecs, joinProcedure);
        }

        private Map<LocationVariable, Term> buildPreconditions() {
            final Map<LocationVariable, Term> result = new LinkedHashMap<LocationVariable, Term>();
            for (LocationVariable heap : heaps) {
                if (requires.get(heap) != null) {
                    result.put(heap, convertToFormula(requires.get(heap)));
                }
            }
            return result;
        }

        private Map<LocationVariable, Term> buildPostconditions() {
            final Map<LocationVariable,Term> postconditions =
                    new LinkedHashMap<LocationVariable,Term>();
            for (LocationVariable heap : heaps) {
                if (ensures.get(heap) != null) {
                    postconditions.put(heap, buildPostcondition(heap));
                }
            }
            return postconditions;
        }

        private Term buildPostcondition(final LocationVariable heap) {
            final Term breakPostcondition =
                    conditionPostconditions(variables.breakFlags, breaks);
            final Term continuePostcondition =
                    conditionPostconditions(variables.continueFlags, continues);
            final Term returnPostcondition =
                    conditionPostcondition(variables.returnFlag, returns);
            final Term throwPostcondition = buildThrowPostcondition();
            // TODO Why do we handle the two cases differently? Surely has something to do with transactions.
            if (heap == services.getTypeConverter().getHeapLDT().getHeap()) {
                if (behavior == Behavior.NORMAL_BEHAVIOR) {
                    return and(buildNormalTerminationCondition(),
                               convertToFormula(ensures.get(heap)));
                }
                else if (behavior == Behavior.BREAK_BEHAVIOR) {
                    return and(buildBreakTerminationCondition(), breakPostcondition);
                }
                else if (behavior == Behavior.CONTINUE_BEHAVIOR) {
                    return and(buildContinueTerminationCondition(), continuePostcondition);
                }
                else if (behavior == Behavior.RETURN_BEHAVIOR) {
                    return and(buildReturnTerminationCondition(), returnPostcondition);
                }
                else if (behavior == Behavior.EXCEPTIONAL_BEHAVIOR) {
                    return and(buildThrowTerminationCondition(), throwPostcondition);
                }
                else {
                    return and(
                        imp(buildNormalTerminationCondition(), convertToFormula(ensures.get(heap))),
                        breakPostcondition,
                        continuePostcondition,
                        returnPostcondition,
                        throwPostcondition
                    );
                }
            }
            else {
                if (behavior == Behavior.NORMAL_BEHAVIOR) {
                    return and(buildNormalTerminationCondition(),
                               convertToFormula(ensures.get(heap)));
                }
                else {
                    return imp(buildNormalTerminationCondition(),
                               convertToFormula(ensures.get(heap)));
                }
            }
        }

        private Term conditionPostconditions(final Map<Label, ProgramVariable> flags,
                                             final Map<Label, Term> postconditions) {
            Term result = tt();
            for (Label label : flags.keySet()) {
                result = and(result,
                             conditionPostcondition(flags.get(label),
                                                    postconditions.get(label)));
            }
            return result;
        }

        private Term conditionPostcondition(final ProgramVariable flag, final Term postcondition) {
            Term result = tt();
            if (flag != null) {
                result = imp(
                    equals(services.getTypeConverter().convertToLogicElement(flag), TRUE()),
                    postcondition == null ? tt() : postcondition
                );
            }
            return result;
        }

        private Term buildThrowPostcondition()
        {
            return imp(
                not(equals(var(variables.exception), NULL())),
                and(convertToFormula(signals), convertToFormula(signalsOnly))
            );
        }

        private Term buildNormalTerminationCondition()
        {
            return and(
                buildNormalTerminationCondition(variables.breakFlags),
                buildNormalTerminationCondition(variables.continueFlags),
                buildFlagIsCondition(variables.returnFlag, FALSE()),
                buildExceptionIsNullCondition()
            );
        }

        private Term buildBreakTerminationCondition()
        {
            return and(
                buildAbruptTerminationCondition(variables.breakFlags),
                buildNormalTerminationCondition(variables.continueFlags),
                buildFlagIsCondition(variables.returnFlag, FALSE()),
                buildExceptionIsNullCondition()
            );
        }

        private Term buildContinueTerminationCondition()
        {
            return and(
                buildNormalTerminationCondition(variables.breakFlags),
                buildAbruptTerminationCondition(variables.continueFlags),
                buildFlagIsCondition(variables.returnFlag, FALSE()),
                buildExceptionIsNullCondition()
            );
        }

        private Term buildReturnTerminationCondition()
        {
            return and(
                buildNormalTerminationCondition(variables.breakFlags),
                buildNormalTerminationCondition(variables.continueFlags),
                buildFlagIsCondition(variables.returnFlag, TRUE()),
                buildExceptionIsNullCondition()
            );
        }

        private Term buildThrowTerminationCondition()
        {
            return and(
                buildNormalTerminationCondition(variables.breakFlags),
                buildNormalTerminationCondition(variables.continueFlags),
                buildFlagIsCondition(variables.returnFlag, FALSE()),
                not(buildExceptionIsNullCondition())
            );
        }

        private Term buildNormalTerminationCondition(final Map<Label, ProgramVariable> flags)
        {
            Term result = tt();
            for (Label label : flags.keySet()) {
                result = and(result, buildFlagIsCondition(flags.get(label), FALSE()));
            }
            return result;
        }

        private Term buildAbruptTerminationCondition(final Map<Label, ProgramVariable> flags)
        {
            Term result = ff();
            for (Label label : flags.keySet()) {
                result = or(result, buildFlagIsCondition(flags.get(label), TRUE()));
            }
            return result;
        }

        private Term buildFlagIsCondition(final ProgramVariable flag, final Term truth)
        {
            Term result = tt();
            if (flag != null) {
                result = equals(var(flag), truth);
            }
            return result;
        }

        private Term buildExceptionIsNullCondition()
        {
            return equals(var(variables.exception), NULL());
        }

        private Map<LocationVariable, Term> buildModifiesClauses()
        {
            return assignables;
        }

        private ImmutableSet<BlockContract>
                    create(final Map<LocationVariable, Term> preconditions,
                           final Map<LocationVariable, Term> postconditions,
                           final Map<LocationVariable, Term> modifiesClauses,
                           final ImmutableList<InfFlowSpec> infFlowSpecs,
                           final JoinProcedure joinProcedure) {
            ImmutableSet<BlockContract> result = DefaultImmutableSet.nil();
            final boolean transactionApplicable =
                    modifiesClauses.get(
                            services.getTypeConverter().getHeapLDT().getSavedHeap()) != null;
            result = result.add(
                new SimpleBlockContract(
                    block, labels, method, diverges.equals(ff()) ? Modality.DIA : Modality.BOX,
                    preconditions, postconditions, modifiesClauses,
                    infFlowSpecs, joinProcedure, variables, transactionApplicable, hasMod)
                );
            if (ifDivergesConditionCannotBeExpressedByAModality()) {
                result = result.add(
                    new SimpleBlockContract(
                        block, labels, method, Modality.DIA,
                        addNegatedDivergesConditionToPreconditions(preconditions),
                        postconditions, modifiesClauses, infFlowSpecs, joinProcedure,
                        variables, transactionApplicable, hasMod)
                    );
            }
            return result;
        }

        private boolean ifDivergesConditionCannotBeExpressedByAModality()
        {
            return !diverges.equals(ff()) && !diverges.equals(tt());
        }

        private Map<LocationVariable, Term> addNegatedDivergesConditionToPreconditions(
                final Map<LocationVariable, Term> preconditions) {
            final Map<LocationVariable, Term> result = new LinkedHashMap<LocationVariable, Term>();
            for (LocationVariable heap : heaps) {
                if (preconditions.get(heap) != null) {
                    result.put(heap, and(preconditions.get(heap), not(convertToFormula(diverges))));
                }
            }
            return result;
        }

    }

    private static final class Combinator extends TermBuilder {

        private final BlockContract[] contracts;

        private BlockContract.Variables placeholderVariables;
        private Map<LocationVariable, LocationVariable> remembranceVariables;

        private final Map<LocationVariable, Term> preconditions;
        private final Map<LocationVariable, Term> postconditions;
        private final Map<LocationVariable, Term> modifiesClauses;

        public Combinator(final ImmutableSet<BlockContract> contracts, final Services services) {
            super(services.getTermFactory(), services);
            this.contracts = sort(contracts);
            preconditions = new LinkedHashMap<LocationVariable, Term>();
            postconditions = new LinkedHashMap<LocationVariable, Term>();
            modifiesClauses = new LinkedHashMap<LocationVariable, Term>();
        }

        private BlockContract[] sort(final ImmutableSet<BlockContract> contracts)
        {
            //sort contracts alphabetically (for determinism)
            BlockContract[] result = contracts.toArray(new BlockContract[contracts.size()]);
            Arrays.sort(result, new Comparator<BlockContract>() {
                public int compare(BlockContract firstContract, BlockContract secondContract) {
                    return firstContract.getName().compareTo(secondContract.getName());
                }
            });
            return result;
        }

        // Similar to ContractFactory#union.
        private BlockContract combine() {
            assert contracts.length > 0;
            if (contracts.length == 1) {
                return contracts[0];
            }
            final BlockContract head = contracts[0];
            for (int i = 1; i < contracts.length; i++) {
                assert contracts[i].getBlock().equals(head.getBlock());
            }
            placeholderVariables = head.getPlaceholderVariables();
            remembranceVariables = placeholderVariables.combineRemembranceVariables();
            for (BlockContract contract : contracts) {
                addConditionsFrom(contract);
            }
            Map<LocationVariable,Boolean> hasMod = new LinkedHashMap<LocationVariable, Boolean>();
            for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            	boolean hm = false;
                for (int i = 1; i < contracts.length && !hm; i++) {
                    hm = contracts[i].hasModifiesClause(heap);
                }
            	hasMod.put(heap, hm);
            }
            return new SimpleBlockContract(head.getBlock(), head.getLabels(),
                                           head.getMethod(), head.getModality(), preconditions,
                                           postconditions, modifiesClauses, head.getInfFlowSpecs(),
                                           head.getJoinProcedure(),
                                           placeholderVariables, head.isTransactionApplicable(),
                                           hasMod);
        }

        private void addConditionsFrom(final BlockContract contract)
        {
            for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                final Term precondition = addPreconditionFrom(contract, heap);
                addPostconditionFrom(precondition, contract, heap);
                addModifiesClauseFrom(contract, heap);
            }
        }

        private Term addPreconditionFrom(final BlockContract contract, final LocationVariable heap) {
            final Term precondition =
                    contract.getPrecondition(heap, placeholderVariables.self,
                                             placeholderVariables.remembranceHeaps, services);
            if (precondition != null) {
                preconditions.put(heap, orPossiblyNull(preconditions.get(heap), precondition));
            }
            return precondition;
        }

        private void addPostconditionFrom(final Term precondition, final BlockContract contract,
                                          final LocationVariable heap) {
            final Term unconditionalPostcondition =
                    contract.getPostcondition(heap, placeholderVariables, services);
            if (unconditionalPostcondition != null) {
                final Term conditionalPostcondition =
                        imp(preify(precondition), unconditionalPostcondition);
                postconditions.put(heap,
                                   andPossiblyNull(postconditions.get(heap),
                                                   conditionalPostcondition));
            }
        }

        private void addModifiesClauseFrom(final BlockContract contract,
                                           final LocationVariable heap) {
            final Term additionalModifiesClause =
                    contract.getModifiesClause(heap, placeholderVariables.self, services);
            if (additionalModifiesClause != null) {
                modifiesClauses.put(heap,
                                    unionPossiblyNull(modifiesClauses.get(heap),
                                                      additionalModifiesClause));
            }
        }

        private Term orPossiblyNull(final Term currentCondition, final Term additionalCondition) {
            if (currentCondition == null) {
                return additionalCondition;
            }
            else {
                return or(currentCondition, additionalCondition);
            }
        }

        private Term andPossiblyNull(final Term currentCondition, final Term additionalCondition) {
            if (currentCondition == null) {
                return additionalCondition;
            }
            else {
                return and(currentCondition, additionalCondition);
            }
        }

        private Term unionPossiblyNull(final Term currentLocationSet,
                                       final Term additionalLocationSet) {
            if (currentLocationSet == null){
                return additionalLocationSet;
            }
            else if (additionalLocationSet == null) {
                return currentLocationSet;
            }
            else {
                return union(currentLocationSet, additionalLocationSet);
            }
        }

        // Replaces variables in formula by remembrance variables.
        private Term preify(final Term formula) {
            if (formula == null) {
                return tt();
            }
            else {
                final Map<Term, Term> replacementMap = new LinkedHashMap<Term, Term>();
                for (Map.Entry<LocationVariable, LocationVariable> remembranceVariable
                        : remembranceVariables.entrySet()) {
                    if (remembranceVariable.getValue() != null) {
                        replacementMap.put(var(remembranceVariable.getKey()),
                                           var(remembranceVariable.getValue()));
                    }
                }
                return new OpReplacer(replacementMap, services.getTermFactory()).replace(formula);
            }
        }

    }

}