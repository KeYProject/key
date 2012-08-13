package de.uka.ilkd.key.speclang;

import java.util.*;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;

public final class SimpleBlockContract implements BlockContract {

    public static BlockContract combine(ImmutableSet<BlockContract> contracts, Services services)
    {
        return new Combiner(contracts, services).combine();
    }

	private final StatementBlock block;
    private final IProgramMethod method;
    private final Modality modality;

    private final Map<LocationVariable, Term> preconditions;
    private final Map<LocationVariable, Term> postconditions;
    private final Map<LocationVariable, Term> modifiesConditions;

    private final Variables variables;

    private final boolean transaction;

    public SimpleBlockContract(final StatementBlock block,
                               final IProgramMethod method,
                               final Modality modality,
                               final Map<LocationVariable, Term> preconditions,
                               final Map<LocationVariable, Term> postconditions,
                               final Map<LocationVariable, Term> modifiesConditions,
                               final Variables variables,
                               final boolean transaction)
    {
        assert block != null;
        assert method != null;
        assert modality != null;
        assert preconditions != null;
        assert postconditions != null;
        assert variables.breakFlags != null;
        assert variables.continueFlags != null;
        assert variables.exception != null;
        assert variables.remembranceHeaps != null && variables.remembranceHeaps.size() > 0;
        assert variables.remembranceLocalVariables != null;
        this.block = block;
        this.method = method;
        this.modality = modality;
        this.preconditions = preconditions;
        this.postconditions = postconditions;
        this.modifiesConditions = modifiesConditions;
        this.variables = variables;
        this.transaction = transaction;
    }

    @Override
    public StatementBlock getBlock()
    {
        return block;
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
    public boolean getTransaction()
    {
        return transaction;
    }

    // TODO Assertions.

    @Override
    public Term getPrecondition(final LocationVariable heap,
                                final ProgramVariable self,
                                final Map<LocationVariable, LocationVariable> remembranceHeaps,
                                final Services services)
    {
        final Map<ProgramVariable, ProgramVariable> replacementMap = createReplacementMap(
            new Variables(self, null, null, null, null, null, remembranceHeaps, null), services
        );
        final OpReplacer replacer = new OpReplacer(replacementMap);
        return replacer.replace(preconditions.get(heap));
    }

    @Override
    public Term getPrecondition(final LocationVariable heapVariable,
                                final Term heap,
                                final Term self,
                                final Map<LocationVariable, Term> remembranceHeaps,
                                final Services services)
    {
        final Map<Term, Term> replacementMap = createReplacementMap(
            heap, new Terms(self, null, null, null, null, null, remembranceHeaps, null), services
        );
        final OpReplacer replacer = new OpReplacer(replacementMap);
        return replacer.replace(preconditions.get(heapVariable));
    }

    @Override
    public Term getPrecondition(final LocationVariable heap, final Services services)
    {
        return getPrecondition(heap, variables.self, variables.remembranceHeaps, services);
    }

    @Override
    public Term getPostcondition(final LocationVariable heap, final Variables variables, final Services services)
    {
        final OpReplacer replacer = new OpReplacer(createReplacementMap(variables, services));
        return replacer.replace(postconditions.get(heap));
    }

    @Override
    public Term getPostcondition(final LocationVariable heapVariable, final Term heap, final Terms terms, final Services services)
    {
        final OpReplacer replacer = new OpReplacer(createReplacementMap(heap, terms, services));
        return replacer.replace(postconditions.get(heapVariable));
    }

    @Override
    public Term getPostcondition(final LocationVariable heap, final Services services)
    {
        return getPostcondition(heap, variables, services);
    }

    @Override
    public Term getModifiesCondition(final LocationVariable heap, final ProgramVariable self, final Services services)
    {
        final Map<ProgramVariable, ProgramVariable> replacementMap = createReplacementMap(
            new Variables(self, null, null, null, null, null, null, null), services
        );
        final OpReplacer replacer = new OpReplacer(replacementMap);
        return replacer.replace(modifiesConditions.get(heap));
    }

    @Override
    public Term getModifiesCondition(final LocationVariable heapVariable, final Term heap, final Term self, final Services services)
    {
        final Map<Term, Term> replacementMap = createReplacementMap(
            heap, new Terms(self, null, null, null, null, null, null, null), services
        );
        final OpReplacer replacer = new OpReplacer(replacementMap);
        return replacer.replace(modifiesConditions.get(heapVariable));
    }

    @Override
    public Term getModifiesCondition(final LocationVariable heap, final Services services)
    {
        return getModifiesCondition(heap, variables.self, services);
    }

    @Override
    public void visit(final Visitor visitor)
    {
        visitor.performActionOnBlockContract(this);
    }

    @Override
    public String getName()
    {
        return "Block Contract";
    }

    @Override
    public String getDisplayName()
    {
        return getName();
    }

    @Override
    public String getHtmlText(final Services services)
    {
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
            if (modifiesConditions.get(heap) != null) {
                mods = mods + "<br><b>mod" + (heap == baseHeap ? "" : "[" + heap + "]") + "</b> "
                        + LogicPrinter.escapeHTML(LogicPrinter.quickPrintTerm(modifiesConditions.get(heap), services), false);
                /*if (heap == baseHeap && !hasRealModifiesClause) {
                    mods = mods + "<b>, creates no new objects</b>";
                }*/
            }
        }
        String pres = "";
        for (LocationVariable heap : heapLDT.getAllHeaps()) {
            if (preconditions.get(heap) != null) {
                pres = pres + "<br><b>pre" + (heap == baseHeap ? "" : "[" + heap + "]") + "</b> "
                        + LogicPrinter.escapeHTML(LogicPrinter.quickPrintTerm(preconditions.get(heap), services), false);
            }
        }
        String posts = "";
        for (LocationVariable heap : heapLDT.getAllHeaps()) {
            if (postconditions.get(heap) != null) {
                posts = posts + "<br><b>post" + (heap == baseHeap ? "" : "[" + heap + "]") + "</b> "
                         + LogicPrinter.escapeHTML(LogicPrinter.quickPrintTerm(postconditions.get(heap), services), false);
            }
        }
        return "<html>"
                + "<i>" + LogicPrinter.escapeHTML(stringBuilder.toString(), false) + "</i>"
                + pres
                + posts
                + mods
                + "<br><b>termination</b> "
                + getModality()
                /*+ (transactionApplicableContract() ? "<br><b>transaction applicable</b>" : "")*/
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
                                final Map<LocationVariable,Term> newModifiesConditions,
                                final Variables newVariables)
    {
        return new SimpleBlockContract(newBlock, method, modality, newPreconditions, newPostconditions, newModifiesConditions, newVariables, transaction);
    }

    private Map<ProgramVariable, ProgramVariable> createReplacementMap(final Variables newVariables, final Services services)
    {
        final VariableReplacementMap result = new VariableReplacementMap();
        result.replaceSelf(variables.self, newVariables.self);
        result.replaceFlags(variables.breakFlags, newVariables.breakFlags);
        result.replaceFlags(variables.continueFlags, newVariables.continueFlags);
        result.replaceVariable(variables.returnFlag, newVariables.returnFlag);
        result.replaceVariable(variables.result, newVariables.result);
        result.replaceVariable(variables.exception, newVariables.exception);
        result.replaceRemembranceHeaps(variables.remembranceHeaps, newVariables.remembranceHeaps, services);
        result.replaceRemembranceLocalVariables(variables.remembranceLocalVariables, newVariables.remembranceLocalVariables);
        return result;
    }

    private Map<Term, Term> createReplacementMap(final Term newHeap, final Terms newTerms, final Services services)
    {
        final TermReplacementMap result = new TermReplacementMap();
        result.replaceHeap(newHeap, services);
        result.replaceSelf(variables.self, newTerms.self);
        result.replaceFlags(variables.breakFlags, newTerms.breakFlags);
        result.replaceFlags(variables.continueFlags, newTerms.continueFlags);
        result.replaceVariable(variables.returnFlag, newTerms.returnFlag);
        result.replaceVariable(variables.result, newTerms.result);
        result.replaceVariable(variables.exception, newTerms.exception);
        result.replaceRemembranceHeaps(variables.remembranceHeaps, newTerms.remembranceHeaps, services);
        result.replaceRemembranceLocalVariables(variables.remembranceLocalVariables, newTerms.remembranceLocalVariables);
        return result;
    }

    private static class VariableReplacementMap extends LinkedHashMap<ProgramVariable, ProgramVariable> {

        public void replaceSelf(final ProgramVariable oldSelf, final ProgramVariable newSelf)
        {
            if (newSelf != null) {
                assert newSelf.sort().extendsTrans(oldSelf.sort());
                put(oldSelf, newSelf);
            }
        }

        public void replaceFlags(final Map<Label, ProgramVariable> oldFlags, final Map<Label, ProgramVariable> newFlags)
        {
            if (newFlags != null) {
                assert newFlags.size() == oldFlags.size();
                for (Map.Entry<Label, ProgramVariable> oldFlag : oldFlags.entrySet()) {
                    replaceVariable(oldFlag.getValue(), newFlags.get(oldFlag.getKey()));
                }
            }
        }

        public void replaceVariable(final ProgramVariable oldVariable, final ProgramVariable newVariable)
        {
            if (newVariable != null) {
                assert oldVariable.sort().equals(newVariable.sort());
                put(oldVariable, newVariable);
            }
        }

        public void replaceRemembranceHeaps(final Map<LocationVariable, LocationVariable> oldRemembranceHeaps,
                                            final Map<LocationVariable, LocationVariable> newRemembranceHeaps,
                                            final Services services)
        {
            if (newRemembranceHeaps != null) {
                for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                    if (newRemembranceHeaps.get(heap) != null) {
                        final LocationVariable oldRemembranceHeap = oldRemembranceHeaps.get(heap);
                        final LocationVariable newRemembranceHeap = newRemembranceHeaps.get(heap);
                        assert oldRemembranceHeap.sort().equals(newRemembranceHeap.sort());
                        put(oldRemembranceHeap, newRemembranceHeap);
                    }
                }
            }
        }

        public void replaceRemembranceLocalVariables(final Map<LocationVariable, LocationVariable> oldRemembranceLocalVariables,
                                                     final Map<LocationVariable, LocationVariable> newRemembranceLocalVariables)
        {
            if (newRemembranceLocalVariables != null) {
                for (LocationVariable localVariable : oldRemembranceLocalVariables.keySet()) {
                    if (newRemembranceLocalVariables.get(localVariable) != null) {
                        LocationVariable oldRemembranceLocalVariable = oldRemembranceLocalVariables.get(localVariable);
                        LocationVariable newRemembranceLocalVariable = newRemembranceLocalVariables.get(localVariable);
                        assert oldRemembranceLocalVariable.sort().equals(newRemembranceLocalVariable.sort());
                        put(oldRemembranceLocalVariable, newRemembranceLocalVariable);
                    }
                }
            }
        }

    }

    private static class TermReplacementMap extends LinkedHashMap<Term, Term> {

        private static final TermBuilder TB = TermBuilder.DF;

        public void replaceHeap(final Term newHeap, final Services services)
        {
            assert newHeap != null;
            assert newHeap.sort().equals(services.getTypeConverter().getHeapLDT().targetSort());
            put(TB.getBaseHeap(services), newHeap);
        }

        public void replaceSelf(final ProgramVariable oldSelf, final Term newSelf)
        {
            if (newSelf != null) {
                assert newSelf.sort().extendsTrans(oldSelf.sort());
                put(TB.var(oldSelf), newSelf);
            }
        }

        public void replaceFlags(final Map<Label, ProgramVariable> oldFlags, final Map<Label, Term> newFlags)
        {
            if (newFlags != null) {
                assert newFlags.size() == oldFlags.size();
                for (Map.Entry<Label, ProgramVariable> oldFlag : oldFlags.entrySet()) {
                    replaceVariable(oldFlag.getValue(), newFlags.get(oldFlag.getKey()));
                }
            }
        }

        public void replaceVariable(final ProgramVariable oldVariable, final Term newVariable)
        {
            if (newVariable != null) {
                assert oldVariable.sort().equals(newVariable.sort());
                put(TB.var(oldVariable), newVariable);
            }
        }

        public void replaceRemembranceHeaps(final Map<LocationVariable, LocationVariable> oldRemembranceHeaps,
                                            final Map<LocationVariable, Term> newRemembranceHeaps,
                                            final Services services)
        {
            if (newRemembranceHeaps != null) {
                for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                    if (newRemembranceHeaps.get(heap) != null) {
                        final LocationVariable oldRemembranceHeap = oldRemembranceHeaps.get(heap);
                        final Term newRemembranceHeap = newRemembranceHeaps.get(heap);
                        assert oldRemembranceHeap.sort().equals(newRemembranceHeap.sort());
                        put(TB.var(oldRemembranceHeap), newRemembranceHeap);
                    }
                }
            }
        }

        public void replaceRemembranceLocalVariables(final Map<LocationVariable, LocationVariable> oldRemembranceLocalVariables,
                                                     final Map<LocationVariable, Term> newRemembranceLocalVariables)
        {
            if (newRemembranceLocalVariables != null) {
                for (LocationVariable localVariable : oldRemembranceLocalVariables.keySet()) {
                    Term newRemembranceLocalVariable = newRemembranceLocalVariables.get(localVariable);
                    if (newRemembranceLocalVariable != null) {
                        assert oldRemembranceLocalVariables.get(localVariable).sort().equals(newRemembranceLocalVariable.sort());
                        put(TB.var(localVariable), newRemembranceLocalVariable);
                    }
                }
            }
        }

    }

    public static final class Creator extends TermBuilder {

        private final StatementBlock block;
        private final IProgramMethod method;
        private final Behavior behavior;
        private final Variables variables;
        private final Map<LocationVariable, Term> requires;
        private final Map<LocationVariable, Term> ensures;
        private final Map<Label, Term> breaks;
        private final Map<Label, Term> continues;
        private final Term returns;
        private final Term signals;
        private final Term signalsOnly;
        private final Term diverges;
        private final Map<LocationVariable, Term> assignables;
        private final boolean strictlyPure;
        private final ImmutableArray<LocationVariable> heaps;

        public Creator(final StatementBlock block,
                       final IProgramMethod method,
                       final Behavior behavior,
                       final Variables variables,
                       final Map<LocationVariable, Term> requires,
                       final Map<LocationVariable, Term> ensures,
                       final Map<Label, Term> breaks,
                       final Map<Label, Term> continues,
                       final Term returns,
                       final Term signals,
                       final Term signalsOnly,
                       final Term diverges,
                       final Map<LocationVariable, Term> assignables,
                       final boolean strictlyPure,
                       final Services services)
        {
            super(services);
            this.block = block;
            this.method = method;
            this.behavior = behavior;
            this.variables = variables;
            this.requires = requires;
            this.ensures = ensures;
            this.breaks = breaks;
            this.continues = continues;
            this.returns = returns;
            this.signals = signals;
            this.signalsOnly = signalsOnly;
            this.diverges = diverges;
            this.assignables = assignables;
            this.strictlyPure = strictlyPure;
            this.heaps = services.getTypeConverter().getHeapLDT().getAllHeaps();
        }

        public ImmutableSet<BlockContract> create()
        {
            final Map<LocationVariable, Term> preconditions = buildPreconditions();
            final Map<LocationVariable, Term> postconditions = buildPostconditions();
            final Map<LocationVariable, Term> modifiesConditions = buildModifiesConditions();
            // TODO Refactor.
            ImmutableSet<BlockContract> result = DefaultImmutableSet.nil();
            final boolean transaction = modifiesConditions.get(services.getTypeConverter().getHeapLDT().getSavedHeap()) != null;
            result = result.add(
                new SimpleBlockContract(
                    block, method, diverges.equals(ff()) ? Modality.DIA : Modality.BOX,
                    preconditions, postconditions, modifiesConditions,
                    variables, transaction
                )
            );
            // TODO better naming: if diverges condition is neither false nor true
            if (!diverges.equals(ff()) && !diverges.equals(tt())) {
                // TODO Extract.
                final Map<LocationVariable, Term> diamondPreconditions = new LinkedHashMap<LocationVariable, Term>();
                for (LocationVariable heap : heaps) {
                    if (preconditions.get(heap) != null) {
                        diamondPreconditions.put(heap, and(preconditions.get(heap), not(convertToFormula(diverges))));
                    }
                }
                result = result.add(
                    new SimpleBlockContract(
                        block, method, Modality.DIA,
                        diamondPreconditions, postconditions, modifiesConditions,
                        variables, transaction
                    )
                );
            }
            return result;
        }

        private Map<LocationVariable, Term> buildPreconditions()
        {
            final Map<LocationVariable, Term> result = new LinkedHashMap<LocationVariable, Term>();
            for (LocationVariable heap : heaps) {
                if (requires.get(heap) != null) {
                    result.put(heap, convertToFormula(requires.get(heap)));
                }
            }
            return result;
        }

        private Map<LocationVariable, Term> buildPostconditions()
        {
            final Map<LocationVariable,Term> postconditions = new LinkedHashMap<LocationVariable,Term>();
            for (LocationVariable heap : heaps) {
                if (ensures.get(heap) != null) {
                    postconditions.put(heap, buildPostcondition(heap));
                }
            }
            return postconditions;
        }

        private Term buildPostcondition(final LocationVariable heap)
        {
            final Term breakPostcondition = conditionPostconditions(variables.breakFlags, breaks);
            final Term continuePostcondition = conditionPostconditions(variables.continueFlags, continues);
            final Term returnPostcondition = conditionPostcondition(variables.returnFlag, returns);
            final Term throwPostcondition = buildThrowPostcondition();
            // TODO Why do we handle the two cases differently?
            if (heap == services.getTypeConverter().getHeapLDT().getHeap()) {
                if (behavior == Behavior.NORMAL_BEHAVIOR) {
                    return and(buildNormalTerminationCondition(), convertToFormula(ensures.get(heap)));
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
                    return and(buildNormalTerminationCondition(), convertToFormula(ensures.get(heap)));
                }
                else {
                    return imp(buildNormalTerminationCondition(), convertToFormula(ensures.get(heap)));
                }
            }
        }

        private Term conditionPostconditions(final Map<Label, ProgramVariable> flags, final Map<Label, Term> postconditions)
        {
            Term result = tt();
            for (Label label : flags.keySet()) {
                result = and(result, conditionPostcondition(flags.get(label), postconditions.get(label)));
            }
            return result;
        }

        private Term conditionPostcondition(final ProgramVariable flag, final Term postcondition)
        {
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

        private Map<LocationVariable, Term> buildModifiesConditions()
        {
            // TODO Is there really nothing to do here?
            return assignables;
        }

    }

    private static final class Combiner extends TermBuilder
    {

        private final BlockContract[] contracts;

        public Combiner(final ImmutableSet<BlockContract> contracts, final Services services)
        {
            super(services);
            this.contracts = sort(contracts);
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

        // TODO Refactor.

        // Similar to ContractFactory#union.
        private BlockContract combine()
        {
            assert contracts.length > 0;
            if (contracts.length == 1) {
                return contracts[0];
            }
            BlockContract head = contracts[0];
            BlockContract[] tail = Arrays.copyOfRange(contracts, 1, contracts.length);

            for (BlockContract other : tail) {
                assert other.getBlock().equals(head.getBlock());
            }

            BlockContract.Variables placeholderVariables = head.getPlaceholderVariables();

            ImmutableArray<LocationVariable> heaps = services.getTypeConverter().getHeapLDT().getAllHeaps();

            Map<LocationVariable, Term> preconditions = new LinkedHashMap<LocationVariable, Term>();
            Map<LocationVariable, Term> postconditions = new LinkedHashMap<LocationVariable, Term>();
            Map<LocationVariable, Term> modifiesConditions = new LinkedHashMap<LocationVariable, Term>();
            Map<LocationVariable, LocationVariable> remembranceVariables = placeholderVariables.combineRemembranceVariables();
            for (LocationVariable heap : heaps) {
                preconditions.put(heap, head.getPrecondition(heap, services));
                Term oldPostcondition = head.getPostcondition(heap, services);
                if (oldPostcondition != null) {
                    postconditions.put(heap, imp(preify(preconditions.get(heap), remembranceVariables), oldPostcondition));
                }
                modifiesConditions.put(heap, head.getModifiesCondition(heap, services));
            }

            for (BlockContract other : tail) {
                for (LocationVariable heap : heaps) {
                    Term additionalPrecondition = other.getPrecondition(heap, placeholderVariables.self, placeholderVariables.remembranceHeaps, services);
                    if (additionalPrecondition != null) {
                        final Term combinedPrecondition;
                        if (preconditions.get(heap) == null) {
                            combinedPrecondition = additionalPrecondition;
                        }
                        else {
                            combinedPrecondition = or(preconditions.get(heap), additionalPrecondition);
                        }
                        preconditions.put(heap, combinedPrecondition);
                    }
                    Term oldAdditionalPostcondition = other.getPostcondition(heap, placeholderVariables, services);
                    if (oldAdditionalPostcondition != null) {
                        final Term additionalPostcondition = imp(preify(additionalPrecondition, remembranceVariables), oldAdditionalPostcondition);
                        final Term combinedPostcondition;
                        if (postconditions.get(heap) == null) {
                            combinedPostcondition = additionalPostcondition;
                        }
                        else {
                            combinedPostcondition = and(postconditions.get(heap), additionalPostcondition);
                        }
                        postconditions.put(heap, combinedPostcondition);
                    }
                }
                for (LocationVariable heap : heaps) {
                    final Term currentModifiesCondition = modifiesConditions.get(heap);
                    final Term additionalModifiesCondition = other.getModifiesCondition(heap, placeholderVariables.self, services);
                    if (currentModifiesCondition != null || additionalModifiesCondition != null) {
                        final Term combinedModifiesCondition;
                        if (currentModifiesCondition == null){
                            combinedModifiesCondition = additionalModifiesCondition;
                        }
                        else if(additionalModifiesCondition == null) {
                            combinedModifiesCondition = currentModifiesCondition;
                        }
                        else {
                            combinedModifiesCondition = union(services, currentModifiesCondition, additionalModifiesCondition);
                        }
                        modifiesConditions.put(heap, combinedModifiesCondition);
                    }
                }
            }
            return new SimpleBlockContract(head.getBlock(), head.getMethod(), head.getModality(), preconditions, postconditions, modifiesConditions, placeholderVariables, head.getTransaction());
        }

        private Term preify(final Term formula, Map<LocationVariable, LocationVariable> remembranceVariables) {
            final Map<Term, Term> replacementMap = new LinkedHashMap<Term, Term>();
            for (Map.Entry<LocationVariable, LocationVariable> remembranceVariable : remembranceVariables.entrySet()) {
                if (remembranceVariable.getValue() != null) {
                    replacementMap.put(var(remembranceVariable.getKey()), var(remembranceVariable.getValue()));
                }
            }
            return new OpReplacer(replacementMap).replace(formula);
        }

    }

}