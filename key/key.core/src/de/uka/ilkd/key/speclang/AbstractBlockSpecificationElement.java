package de.uka.ilkd.key.speclang;

import java.util.Arrays;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Sorted;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.speclang.Contract.OriginalVariables;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.util.InfFlowSpec;

/**
 * Abstract base class for all default implementations of {@link BlockSpecificationElement}.
 */
public abstract class AbstractBlockSpecificationElement
        implements BlockSpecificationElement {

    protected final StatementBlock block;
    protected final List<Label> labels;
    protected final IProgramMethod method;
    protected final Modality modality;
    protected Term instantiationSelf;
    protected final Map<LocationVariable, Term> preconditions;
    protected final Term measuredBy;
    protected final Map<LocationVariable, Term> postconditions;
    protected final Map<LocationVariable, Term> modifiesClauses;
    protected ImmutableList<InfFlowSpec> infFlowSpecs;
    protected final Variables variables;
    protected final boolean transactionApplicable;
    protected final Map<LocationVariable,Boolean> hasMod;
    protected final String baseName;

    public AbstractBlockSpecificationElement(final String baseName,
                               final StatementBlock block,
                               final List<Label> labels,
                               final IProgramMethod method,
                               final Modality modality,
                               final Map<LocationVariable, Term> preconditions,
                               final Term measuredBy,
                               final Map<LocationVariable, Term> postconditions,
                               final Map<LocationVariable, Term> modifiesClauses,
                               final ImmutableList<InfFlowSpec> infFlowSpecs,
                               final Variables variables,
                               final boolean transactionApplicable,
                               final Map<LocationVariable,Boolean> hasMod) {
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
        this.baseName = baseName;
        this.block = block;
        this.labels = labels;
        this.method = method;
        this.modality = modality;
        this.preconditions = preconditions;
        this.measuredBy = measuredBy;
        this.postconditions = postconditions;
        this.modifiesClauses = modifiesClauses;        
        this.infFlowSpecs = infFlowSpecs;
        this.variables = variables;
        this.transactionApplicable = transactionApplicable;
        this.hasMod = hasMod;
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
    public Modality getModality() {
        return modality;
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
    public Term getMby() {
        return measuredBy;
    }

    @Override
    public Term getMby(ProgramVariable selfVar, Services services) {
        final Map<ProgramVariable, ProgramVariable> replacementMap = createReplacementMap(
                new Variables(selfVar, null, null, null, null, null,
                        null, null, null, null, services), services);
        final OpReplacer replacer = new OpReplacer(replacementMap, services.getTermFactory());
        return replacer.replace(measuredBy);
    }

    @Override
    public Term getMby(Map<LocationVariable, Term> heapTerms, Term selfTerm,
            Map<LocationVariable, Term> atPres, Services services) {
        final Map<Term, Term> replacementMap = createReplacementMap(
                null, new Terms(selfTerm, null, null, null, null, null, null, null, null,
                        atPres), services);
        final OpReplacer replacer = new OpReplacer(replacementMap, services.getTermFactory());
        return replacer.replace(measuredBy);
    }

    @Override
    public Term getPrecondition(final LocationVariable heap,
                                final ProgramVariable self,
                                final Map<LocationVariable, LocationVariable> atPres,
                                final Services services) {
        assert heap != null;
        assert (self == null) == (variables.self == null);
        assert atPres != null;
        assert services != null;
        final Map<ProgramVariable, ProgramVariable> replacementMap = createReplacementMap(
            new Variables(self, null, null, null, null, null,
                    null, null, null, atPres, services), services
        );
        final OpReplacer replacer = new OpReplacer(replacementMap, services.getTermFactory());
        return replacer.replace(preconditions.get(heap));
    }

    @Override
    public Term getPrecondition(final LocationVariable heapVariable,
                                final Term heap,
                                final Term self,
                                final Map<LocationVariable, Term> atPres,
                                final Services services) {
        assert heapVariable != null;
        assert heap != null;
        assert (self == null) == (variables.self == null);
        assert atPres != null;
        assert services != null;
        final Map<Term, Term> replacementMap = createReplacementMap(
            heap, new Terms(self, null, null, null, null, null, null, null, null, atPres), services
        );
        final OpReplacer replacer = new OpReplacer(replacementMap, services.getTermFactory());
        return replacer.replace(preconditions.get(heapVariable));
    }

    @Override
    public Term getPrecondition(final LocationVariable heap, final Services services) {
        return getPrecondition(heap, variables.self, variables.outerRemembranceVariables,
                services);
    }
    
    @Override
    public Term getPrecondition(LocationVariable heap, Variables variables, Services services) {
        assert heap != null;
        assert variables != null;
        assert (variables.self == null) == (this.variables.self == null);
        assert services != null;
        final OpReplacer replacer = new OpReplacer(createReplacementMap(variables, services), 
                                                   services.getTermFactory());
        return replacer.replace(preconditions.get(heap));
    }
    
    @Override
    public Term getPrecondition(LocationVariable heapVariable, Term heap,
            Terms terms, Services services) {
        assert heapVariable != null;
        assert heap != null;
        assert terms != null;
        assert (terms.self == null) == (variables.self == null);
        assert services != null;
        final OpReplacer replacer = new OpReplacer(createReplacementMap(heap, terms, services), 
                                                   services.getTermFactory());
        return replacer.replace(preconditions.get(heapVariable));
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
    public Term getPostcondition(final LocationVariable heap, final Services services) {
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
                createReplacementMap(new Variables(self, null, null, null, null, null,
                                                   null, null, null, null, services),
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
            heap, new Terms(self, null, null, null, null, null, null, null, null, null), services
        );
        final OpReplacer replacer = new OpReplacer(replacementMap, services.getTermFactory());
        return replacer.replace(modifiesClauses.get(heapVariable));
    }

    @Override
    public Term getModifiesClause(final LocationVariable heap, final Services services) {
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


    @Override
    public boolean hasMby() {
        return measuredBy != null;
    }

    @Override
    public boolean hasInfFlowSpecs() {
        return infFlowSpecs != null;
    }

    @Override
    public void setInstantiationSelf(Term selfInstantiation) {
        this.instantiationSelf = selfInstantiation;
    }

    @Override
    public Term getInstantiationSelfTerm() {
        return instantiationSelf;
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

    public Term getAssignable(LocationVariable heap) {
        return modifiesClauses.get(heap);
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
        }
        else if (method.isConstructor()) {
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
        String mods = "";
        Term baseHeapTerm = services.getTermBuilder().var(baseHeap);
        for (LocationVariable heap : heapLDT.getAllHeaps()) {
            Term modifiesClause = getModifiesClause(heap, services.getTermBuilder().var(heap), terms.self, services);
            if (modifiesClause != null) {
                mods = mods + "\nmod" + (heap == baseHeap ? "" : "[" + heap + "]") + " "
                        + StringUtil.trim(LogicPrinter.quickPrintTerm(modifiesClause, services));
                /*if (heap == baseHeap && !hasRealModifiesClause) {
                    mods = mods + "<b>, creates no new objects</b>";
                }*/
            }
        }
        String pres = "";
        for (LocationVariable heap : heapLDT.getAllHeaps()) {
            Term precondition = getPrecondition(heap, baseHeapTerm, terms.self, terms.remembranceHeaps, services);
            if (precondition != null) {
                pres = pres + "\npre" + (heap == baseHeap ? "" : "[" + heap + "]") + " "
                        + StringUtil.trim(LogicPrinter.quickPrintTerm(precondition, services));
            }
        }
        String posts = "";
        for (LocationVariable heap : heapLDT.getAllHeaps()) {
            Term postcondition = getPostcondition(heap, baseHeapTerm, terms, services);
            if (postcondition != null) {
                posts = posts + "\npost" + (heap == baseHeap ? "" : "[" + heap + "]") + " "
                         + StringUtil.trim(LogicPrinter.quickPrintTerm(postcondition, services));
            }
        }
        return stringBuilder.toString() 
                + pres
                + posts
                + mods
                + "termination "
                + getModality()
                /*+ (transactionApplicableContract() ? "<br><b>transactionApplicable applicable</b>" : "")*/
                ;
    }

    public OriginalVariables getOrigVars() {
        return variables.toOrigVars();
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        AbstractBlockSpecificationElement other = (AbstractBlockSpecificationElement) obj;
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
        result.replaceRemembranceHeaps(variables.outerRemembranceHeaps,
                newVariables.outerRemembranceHeaps,
                services);
        result.replaceRemembranceLocalVariables(variables.outerRemembranceVariables,
                         newVariables.outerRemembranceVariables,
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
        result.replaceRemembranceHeaps(variables.outerRemembranceHeaps,
                newTerms.outerRemembranceHeaps,
                services);
        result.replaceRemembranceLocalVariables(variables.outerRemembranceVariables,
                         newTerms.outerRemembranceVariables,
                         services);
        return result;
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
    


    protected static abstract class Creator<T extends BlockSpecificationElement>
            extends TermBuilder {

        private final String baseName;
        private final StatementBlock block;
        private final List<Label> labels;
        private final IProgramMethod method;
        private final Behavior behavior;
        private final Variables variables;
        private final Term measuredBy;
        private final Map<LocationVariable, Term> requires;
        private final Map<LocationVariable, Term> ensures;
        private final ImmutableList<InfFlowSpec> infFlowSpecs;
        private final Map<Label, Term> breaks;
        private final Map<Label, Term> continues;
        private final Term returns;
        private final Term signals;
        private final Term signalsOnly;
        private final Term diverges;
        private final Map<LocationVariable, Term> assignables;
        private final ImmutableList<LocationVariable> heaps;
        private final Map<LocationVariable,Boolean> hasMod;

        public Creator(final String baseName,
                       final StatementBlock block,
                       final List<Label> labels,
                       final IProgramMethod method,
                       final Behavior behavior,
                       final Variables variables,
                       final Map<LocationVariable, Term> requires,
                       final Term measuredBy,
                       final Map<LocationVariable, Term> ensures,
                       final ImmutableList<InfFlowSpec> infFlowSpecs,
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
            this.baseName = baseName;
            this.block = block;
            this.labels = labels;
            this.method = method;
            this.behavior = behavior;
            this.variables = variables;
            this.requires = requires;
            this.measuredBy = measuredBy;
            this.ensures = ensures;
            this.infFlowSpecs = infFlowSpecs;
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

        public ImmutableSet<T> create() {
            return create(buildPreconditions(), buildPostconditions(),
                          buildModifiesClauses(), infFlowSpecs);
        }

        private Map<LocationVariable, Term> buildPreconditions() {
            final Map<LocationVariable, Term> result = new LinkedHashMap<LocationVariable, Term>();
            for (LocationVariable heap : heaps) {     
                // Add JML precondition to precondition
                if (requires.get(heap) != null) {
                    result.put(heap, convertToFormula(requires.get(heap)));
                }
                
                // Add measured by term to precondition
                Term old = result.get(heap);
                Term mbyTerm;
                
                if (measuredBy != null && !measuredBy.equals(measuredByEmpty())) {
                    Map<Term, Term> replacementMap = new LinkedHashMap<Term, Term>();
                    
                    for (Map.Entry<LocationVariable, LocationVariable> remembranceVariable
                            : variables.outerRemembranceVariables.entrySet()) {
                        if (remembranceVariable.getValue() != null) {
                            replacementMap.put(var(remembranceVariable.getKey()),
                                               var(remembranceVariable.getValue()));
                        }
                    }
                    
                    for (Map.Entry<LocationVariable, LocationVariable> remembranceVariable
                            : variables.outerRemembranceHeaps.entrySet()) {
                        if (remembranceVariable.getValue() != null) {
                            replacementMap.put(var(remembranceVariable.getKey()),
                                               var(remembranceVariable.getValue()));
                        }
                    }
                    
                    mbyTerm = measuredBy(
                            new OpReplacer(replacementMap, services.getTermFactory()).replace(measuredBy));
                } else {
                    mbyTerm = measuredByEmpty();
                }
                

                if (old == null) {
                    result.put(heap, mbyTerm);
                } else {
                    result.put(heap, and(mbyTerm, old));
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

        private ImmutableSet<T>
                    create(final Map<LocationVariable, Term> preconditions,
                           final Map<LocationVariable, Term> postconditions,
                           final Map<LocationVariable, Term> modifiesClauses,
                           final ImmutableList<InfFlowSpec> infFlowSpecs) {
            ImmutableSet<T> result = DefaultImmutableSet.nil();
            final boolean transactionApplicable =
                    modifiesClauses.get(
                            services.getTypeConverter().getHeapLDT().getSavedHeap()) != null;
            result = result.add(
                build(baseName, 
                    block, labels, method, diverges.equals(ff()) ? Modality.DIA : Modality.BOX,
                    preconditions, measuredBy, postconditions, modifiesClauses,
                    infFlowSpecs, variables, transactionApplicable, hasMod)
                );
            if (divergesConditionCannotBeExpressedByAModality()) {
                result = result.add(
                   build(baseName, 
                        block, labels, method, Modality.DIA,
                        addNegatedDivergesConditionToPreconditions(preconditions), measuredBy,
                        postconditions, modifiesClauses, infFlowSpecs, variables,
                        transactionApplicable, hasMod)
                    );
            }
            return result;
        }

        /**
         * 
         * @param baseName
         * @param block
         * @param labels
         * @param method
         * @param modality
         * @param preconditions
         * @param measuredBy
         * @param postconditions
         * @param modifiesClauses
         * @param infFlowSpecs
         * @param variables
         * @param transactionApplicable
         * @param hasMod
         * @return an instance of {@code T} with the specified attributes.
         */
        protected abstract T build(String baseName, StatementBlock block,
                List<Label> labels, IProgramMethod method, Modality modality,
                Map<LocationVariable, Term> preconditions, Term measuredBy,
                Map<LocationVariable, Term> postconditions,
                Map<LocationVariable, Term> modifiesClauses,
                ImmutableList<InfFlowSpec> infFlowSpecs, Variables variables,
                boolean transactionApplicable,
                Map<LocationVariable, Boolean> hasMod);

        private boolean divergesConditionCannotBeExpressedByAModality() {
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

    protected static abstract class Combinator<T extends BlockSpecificationElement> extends TermBuilder {

        protected final T[] contracts;

        protected Variables placeholderVariables;
        protected Map<LocationVariable, LocationVariable> remembranceVariables;

        protected final Map<LocationVariable, Term> preconditions;
        protected final Map<LocationVariable, Term> postconditions;
        protected final Map<LocationVariable, Term> modifiesClauses;

        public Combinator(final T[] contracts, final Services services) {
            super(services.getTermFactory(), services);
            this.contracts = sort(contracts);
            preconditions = new LinkedHashMap<LocationVariable, Term>();
            postconditions = new LinkedHashMap<LocationVariable, Term>();
            modifiesClauses = new LinkedHashMap<LocationVariable, Term>();
        }

        private T[] sort(final T[] contracts)
        {
            //sort contracts alphabetically (for determinism)
            Arrays.sort(contracts, new Comparator<T>() {
                public int compare(T firstContract, T secondContract) {
                    return firstContract.getName().compareTo(secondContract.getName());
                }
            });
            return contracts;
        }

        protected abstract T combine();

        protected void addConditionsFrom(final T contract) {
            for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                final Term precondition = addPreconditionFrom(contract, heap);
                addPostconditionFrom(precondition, contract, heap);
                addModifiesClauseFrom(contract, heap);
            }
        }

        private Term addPreconditionFrom(final T contract, final LocationVariable heap) {
            final Term precondition =
                    contract.getPrecondition(heap, placeholderVariables.self,
                                             placeholderVariables.remembranceHeaps, services);
            if (precondition != null) {
                preconditions.put(heap, orPossiblyNull(preconditions.get(heap), precondition));
            }
            return precondition;
        }

        private void addPostconditionFrom(final Term precondition, final T contract,
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

        private void addModifiesClauseFrom(final T contract,
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
