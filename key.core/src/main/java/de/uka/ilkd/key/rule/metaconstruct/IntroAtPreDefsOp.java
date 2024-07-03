package de.uka.ilkd.key.rule.metaconstruct;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.JavaStatement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MergePointStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.AuxiliaryContract;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.LoopContract;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.speclang.MergeContract;
import de.uka.ilkd.key.speclang.PredicateAbstractionMergeContract;
import de.uka.ilkd.key.speclang.UnparameterizedMergeContract;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Quadruple;

public final class IntroAtPreDefsOp extends AbstractTermTransformer {

    private static final Comparator<LocationVariable> LOCVAR_COMPARATOR
            = Comparator.comparing(o -> o.name());

    public IntroAtPreDefsOp() {
        super(new Name("#introAtPreDefs"), 1);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Term target = term.sub(0);

        // the target term should have a Java block
        final ProgramElement pe = target.javaBlock().program();
        assert pe != null;

        // collect all loops, blocks, and merge point statements in the innermost method frame
        final Quadruple<MethodFrame, ImmutableSet<LoopStatement>, ImmutableSet<StatementBlock>,
                ImmutableSet<MergePointStatement>> frameAndLoopsAndBlocks
                        = collectLoopsBlocksAndMergePointStatements(pe, services);

        final MethodFrame frame = frameAndLoopsAndBlocks.first;
        final ImmutableSet<LoopStatement> loops = frameAndLoopsAndBlocks.second;
        final ImmutableSet<StatementBlock> blocks = frameAndLoopsAndBlocks.third;
        final ImmutableSet<MergePointStatement> mpss = frameAndLoopsAndBlocks.fourth;

        // determine "self"
        Term selfTerm = determineSelfTerm(frame, services);
        // create atPre heap
        final String methodName = frame.getProgramMethod().getName();

        Map<LocationVariable, Term> atPres = new LinkedHashMap<>();
        Map<LocationVariable, LocationVariable> atPreVars = new LinkedHashMap<>();
        Map<LocationVariable, LocationVariable> atPreHeapVars = new LinkedHashMap<>();

        Term atPreUpdate
                = initAtPreUpdate(methodName, atPres, atPreVars, atPreHeapVars, services, tb);
        // create atPre for parameters
        atPreUpdate = updateAtPreUpdateForLoopInvariants(loops, methodName, atPres, atPreVars,
                atPreUpdate, services, tb);
        atPreUpdate = updateAtPreUpdateForBlockAndLoopContracts(blocks, methodName, atPres,
                atPreVars, atPreHeapVars, atPreUpdate, services, tb);
        atPreUpdate = updateAtPreUpdateForMergePointStatements(mpss, methodName, atPres, atPreVars,
                atPreUpdate, services, tb);
        // update loop invariants
        selfTerm = updateLoopInvariants(loops, frame, selfTerm, atPres, services, tb);
        // update merge contracts
        updateMergeContracts(mpss, atPres, services);
        // update block contracts
        updateBlockAndLoopContracts(blocks, loops, atPreVars, atPreHeapVars, services);

        return tb.apply(atPreUpdate, target, null);
    }

    /**
     * Replace the placeholder variables
     * (see {@link AuxiliaryContract#getPlaceholderVariables()})
     * of all block contracts for blocks in {@code blocks} by
     * {@code atPreVars} and {@code atPreHeapVars}
     *
     * @param blocks the blocks whose contracts to update.
     * @param loops the loops whose contracts to update.
     * @param atPreVars all remembrance variables.
     * @param atPreHeapVars all remembrance heaps.
     * @param services services.
     */
    public void updateBlockAndLoopContracts(
            final ImmutableSet<StatementBlock> blocks,
            final ImmutableSet<LoopStatement> loops,
            Map<LocationVariable, LocationVariable> atPreVars,
            Map<LocationVariable, LocationVariable> atPreHeapVars, Services services) {
        updateBlockAndLoopContracts(
                DefaultImmutableSet.<JavaStatement>nil().union(blocks).union(loops),
                atPreVars, atPreHeapVars, services);
    }

    /**
     * Replace the placeholder variables
     * (see {@link AuxiliaryContract#getPlaceholderVariables()})
     * of all block contracts for blocks in {@code blocks} by
     * {@code atPreVars} and {@code atPreHeapVars}
     *
     * @param statements the blocks and loops whose contracts to update.
     * @param atPreVars all remembrance variables.
     * @param atPreHeapVars all remembrance heaps.
     * @param services services.
     */
    public void updateBlockAndLoopContracts(
            final ImmutableSet<? extends JavaStatement> statements,
            Map<LocationVariable, LocationVariable> atPreVars,
            Map<LocationVariable, LocationVariable> atPreHeapVars, Services services) {
        for (JavaStatement statement : statements) {
            ImmutableSet<AuxiliaryContract> contracts = DefaultImmutableSet.nil();

            if (statement instanceof StatementBlock) {
                StatementBlock block = (StatementBlock) statement;

                for (BlockContract c
                        : services.getSpecificationRepository().getBlockContracts(block)) {
                    contracts = contracts.add(c);
                }

                for (LoopContract c
                        : services.getSpecificationRepository().getLoopContracts(block)) {
                    contracts = contracts.add(c);
                }
            } else {
                LoopStatement loop = (LoopStatement) statement;

                for (LoopContract c
                        : services.getSpecificationRepository().getLoopContracts(loop)) {
                    contracts = contracts.add(c);
                }
            }

            for (AuxiliaryContract contract : contracts) {
                Map<LocationVariable, LocationVariable> nonHeapVars = new LinkedHashMap<>();
                nonHeapVars.putAll(atPreVars);
                atPreHeapVars.forEach((key, val) -> nonHeapVars.remove(key));
                atPreHeapVars.remove(services.getTypeConverter().getHeapLDT().getSavedHeap());

                final AuxiliaryContract.Variables variables
                        = contract.getPlaceholderVariables();
                final AuxiliaryContract.Variables newVariables
                        = new AuxiliaryContract.Variables(variables.self,
                                variables.breakFlags, variables.continueFlags, variables.returnFlag,
                                variables.result, variables.exception, variables.remembranceHeaps,
                                variables.remembranceLocalVariables, atPreHeapVars, nonHeapVars,
                                services);
                final Map<LocationVariable, Term> newPreconditions = new LinkedHashMap<>();
                final Map<LocationVariable, Term> newFreePreconditions = new LinkedHashMap<>();
                final Map<LocationVariable, Term> newPostconditions = new LinkedHashMap<>();
                final Map<LocationVariable, Term> newFreePostconditions = new LinkedHashMap<>();
                final Map<LocationVariable, Term> newModifiesClauses = new LinkedHashMap<>();

                for (LocationVariable heap :
                        services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                    if (heap.name().equals(HeapLDT.SAVED_HEAP_NAME)) {
                        continue;
                    }

                    newPreconditions.put(heap,
                            contract.getPrecondition(heap, newVariables, services));
                    newFreePreconditions.put(heap,
                            contract.getFreePrecondition(heap, newVariables, services));
                    newPostconditions.put(heap,
                            contract.getPostcondition(heap, newVariables, services));
                    newFreePostconditions.put(heap,
                            contract.getFreePostcondition(heap, newVariables, services));
                    newModifiesClauses.put(heap,
                            contract.getModifiesClause(heap, newVariables.self, services));
                }
                updateBlockOrLoopContract(statement, contract, newVariables,
                        newPreconditions, newFreePreconditions,
                        newPostconditions, newFreePostconditions,
                        newModifiesClauses, services);
            }
        }
    }

    private Term initAtPreUpdate(final String methodName, Map<LocationVariable, Term> atPres,
            Map<LocationVariable, LocationVariable> atPreVars,
            Map<LocationVariable, LocationVariable> atPreHeapVars, Services services,
            final TermBuilder tb) {
        Term atPreUpdate = null;
        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            final LocationVariable l
                    = tb.heapAtPreVar(heap.name() + "Before_" + methodName, heap.sort(), true);
            // buf fix. see #1197
            services.getNamespaces().programVariables().addSafely(l);
            final Term u = tb.elementary(l, tb.var(heap));
            if (atPreUpdate == null) {
                atPreUpdate = u;
            } else {
                atPreUpdate = tb.parallel(atPreUpdate, u);
            }

            atPres.put(heap, tb.var(l));
            atPreVars.put(heap, l);
            atPreHeapVars.put(heap, l);
        }
        return atPreUpdate;
    }

    private Term determineSelfTerm(final MethodFrame frame, Services services) {
        Term selfTerm;
        final ExecutionContext ec = (ExecutionContext) frame.getExecutionContext();
        final ReferencePrefix rp = ec.getRuntimeInstance();
        if (rp == null || rp instanceof TypeReference) {
            selfTerm = null;
        } else {
            selfTerm = services.getTypeConverter().convertToLogicElement(rp);
        }
        return selfTerm;
    }

    private Quadruple<MethodFrame, ImmutableSet<LoopStatement>, ImmutableSet<StatementBlock>,
            ImmutableSet<MergePointStatement>>
            collectLoopsBlocksAndMergePointStatements(final ProgramElement pe, Services services) {
        return new JavaASTVisitor(pe, services) {
            private MethodFrame frame = null;
            private ImmutableSet<LoopStatement> loops
                    = DefaultImmutableSet.nil();
            private ImmutableSet<StatementBlock> blocks = DefaultImmutableSet.nil();
            private ImmutableSet<MergePointStatement> mpss
                    = DefaultImmutableSet.nil();

            @Override
            protected void doDefaultAction(SourceElement node) {
                if (node instanceof MethodFrame && frame == null) {
                    frame = (MethodFrame) node;
                } else if (frame == null && node instanceof LoopStatement) {
                    loops = loops.add((LoopStatement) node);
                } else if (frame == null && node instanceof StatementBlock) {
                    blocks = blocks.add((StatementBlock) node);
                } else if (frame == null && node instanceof MergePointStatement) {
                    mpss = mpss.add((MergePointStatement) node);
                }
            }

            public Quadruple<MethodFrame, ImmutableSet<LoopStatement>,
                    ImmutableSet<StatementBlock>, ImmutableSet<MergePointStatement>>
                    run() {
                walk(root());
                return new Quadruple<>(frame, loops, blocks, mpss);
            }
        }.run();
    }

    private Term updateAtPreUpdateForLoopInvariants(final ImmutableSet<LoopStatement> loops,
            final String methodName, Map<LocationVariable, Term> atPres,
            Map<LocationVariable, LocationVariable> atPreVars, Term atPreUpdate, Services services,
            final TermBuilder tb) {
        for (LoopStatement loop : loops) {
            LoopSpecification inv = services.getSpecificationRepository().getLoopSpec(loop);
            if (inv != null) {
                // Nasty bug! The order of these things was not constant! Would
                // fail indeterministically
                // when reloading. Better sort the variables.
                List<LocationVariable> keys
                        = new ArrayList<>(inv.getInternalAtPres().keySet());
                keys.sort(LOCVAR_COMPARATOR);
                for (LocationVariable var : keys) {
                    if (atPres.containsKey(var)) {
                        // heaps have already been considered, or more than one
                        // loop
                        continue;
                    }
                    final LocationVariable l = tb.heapAtPreVar(var.name() + "Before_" + methodName,
                            var.sort(), true);
                    services.getNamespaces().programVariables().addSafely(l);
                    final Term u = tb.elementary(l, tb.var(var));
                    if (atPreUpdate == null) {
                        atPreUpdate = u;
                    } else {
                        atPreUpdate = tb.parallel(atPreUpdate, u);
                    }
                    atPres.put(var, tb.var(l));
                    atPreVars.put(var, l);
                }
            }
        }
        return atPreUpdate;
    }

    private Term updateAtPreUpdateForBlockAndLoopContracts(
            final ImmutableSet<StatementBlock> blocks, final String methodName,
            Map<LocationVariable, Term> atPres, Map<LocationVariable, LocationVariable> atPreVars,
            Map<LocationVariable, LocationVariable> atPreHeapVars, Term atPreUpdate,
            Services services, final TermBuilder tb) {
        for (StatementBlock block : blocks) {
            ImmutableSet<AuxiliaryContract> contracts = DefaultImmutableSet.nil();

            for (BlockContract c : services.getSpecificationRepository().getBlockContracts(block)) {
                contracts = contracts.add(c);
            }
            for (LoopContract c : services.getSpecificationRepository().getLoopContracts(block)) {
                contracts = contracts.add(c);
            }

            for (AuxiliaryContract contract : contracts) {
                List<LocationVariable> keys = new ArrayList<>(
                        contract.getPlaceholderVariables().outerRemembranceVariables.keySet());

                keys.sort(LOCVAR_COMPARATOR);
                for (LocationVariable var : keys) {
                    if (atPres.containsKey(var)) {
                        continue;
                    }
                    final LocationVariable l = tb.heapAtPreVar(var.name() + "Before_" + methodName,
                            var.sort(), true);
                    services.getNamespaces().programVariables().addSafely(l);

                    final Term u = tb.elementary(l, tb.var(var));
                    if (atPreUpdate == null) {
                        atPreUpdate = u;
                    } else {
                        atPreUpdate = tb.parallel(atPreUpdate, u);
                    }

                    atPres.put(var, tb.var(l));
                    atPreVars.put(var, l);
                }

                keys.clear();
                keys.addAll(contract.getPlaceholderVariables().outerRemembranceHeaps.keySet());

                keys.sort(LOCVAR_COMPARATOR);
                for (LocationVariable var : keys) {
                    if (atPres.containsKey(var)) {
                        continue;
                    }
                    final LocationVariable l = tb.heapAtPreVar(var.name() + "Before_" + methodName,
                            var.sort(), true);
                    services.getNamespaces().programVariables().addSafely(l);

                    final Term u = tb.elementary(l, tb.var(var));
                    if (atPreUpdate == null) {
                        atPreUpdate = u;
                    } else {
                        atPreUpdate = tb.parallel(atPreUpdate, u);
                    }

                    atPres.put(var, tb.var(l));
                    atPreVars.put(var, l);
                    atPreHeapVars.put(var, l);
                }
            }
        }
        return atPreUpdate;
    }

    private Term updateAtPreUpdateForMergePointStatements(
            final ImmutableSet<MergePointStatement> mpss, final String methodName,
            Map<LocationVariable, Term> atPres, Map<LocationVariable, LocationVariable> atPreVars,
            Term atPreUpdate, Services services, final TermBuilder tb) {
        for (MergePointStatement mps : mpss) {
            ImmutableSet<MergeContract> mergeContracts
                    = services.getSpecificationRepository().getMergeContracts(mps);

            if (mergeContracts.size() != 1) {
                throw new IllegalArgumentException("Expected exactly one merge contract, got: "+ mergeContracts.size());
            }

            MergeContract spec = mergeContracts.iterator().next();

            assert (spec instanceof UnparameterizedMergeContract
                    || spec instanceof PredicateAbstractionMergeContract)
                : "Unsupported kind of merge contract: " + spec.getClass().getSimpleName();

            if (spec instanceof PredicateAbstractionMergeContract) {
                final PredicateAbstractionMergeContract pamc
                        = (PredicateAbstractionMergeContract) spec;
                List<LocationVariable> keys
                        = new ArrayList<>(pamc.getAtPres().keySet());
                keys.sort(LOCVAR_COMPARATOR);
                for (LocationVariable var : keys) {
                    if (atPres.containsKey(var)) {
                        // heaps and variables in loops have already been considered
                        continue;
                    }
                    final LocationVariable l = tb.heapAtPreVar(var.name() + "Before_" + methodName,
                            var.sort(), true);
                    services.getNamespaces().programVariables().addSafely(l);

                    final Term u = tb.elementary(l, tb.var(var));
                    if (atPreUpdate == null) {
                        atPreUpdate = u;
                    } else {
                        atPreUpdate = tb.parallel(atPreUpdate, u);
                    }
                    atPres.put(var, tb.var(l));
                    atPreVars.put(var, l);
                }
            }
        }
        return atPreUpdate;
    }

    private Term updateLoopInvariants(final ImmutableSet<LoopStatement> loops,
            final MethodFrame frame, Term selfTerm, Map<LocationVariable, Term> atPres,
            Services services, final TermBuilder tb) {
        for (LoopStatement loop : loops) {
            LoopSpecification spec = services.getSpecificationRepository().getLoopSpec(loop);
            if (spec != null) {
                if (selfTerm != null && spec.getInternalSelfTerm() == null) {
                    selfTerm = null; // we're calling a static method from an instance context
                }
                final Term newVariant = spec.getVariant(selfTerm, atPres, services);
                Map<LocationVariable, Term> newMods = new LinkedHashMap<>();
                Map<LocationVariable, ImmutableList<InfFlowSpec>> newInfFlowSpecs
                        = new LinkedHashMap<>();
                // LocationVariable baseHeap =
                // services.getTypeConverter().getHeapLDT().getHeap();
                Map<LocationVariable, Term> newInvariants
                        = new LinkedHashMap<>();
                Map<LocationVariable, Term> newFreeInvariants
                        = new LinkedHashMap<>();
                for (LocationVariable heap : services.getTypeConverter().getHeapLDT()
                        .getAllHeaps()) {
                    final Term term = spec.getInternalModifies()
                            //.get(services.getTypeConverter().getHeapLDT().getHeap());
                            //weigl: prevent NPE
                            .getOrDefault(services.getTypeConverter().getHeapLDT().getHeap(), tb.strictlyNothing());
                    if (heap == services.getTypeConverter().getHeapLDT().getSavedHeap()
                            && tb.strictlyNothing().equalsModIrrelevantTermLabels(term)) {
                        continue;
                    }
                    final Term m = spec.getModifies(heap, selfTerm, atPres, services);
                    final ImmutableList<InfFlowSpec> infFlowSpecs
                            = spec.getInfFlowSpecs(heap, selfTerm, atPres, services);
                    final Term inv = spec.getInvariant(heap, selfTerm, atPres, services);
                    if (inv != null) {
                        newInvariants.put(heap, inv);
                    }
                    if (m != null) {
                        newMods.put(heap, m);
                    }
                    newInfFlowSpecs.put(heap, infFlowSpecs);
                    final Term freeInv = spec.getFreeInvariant(heap, selfTerm, atPres, services);
                    if (freeInv != null) {
                        newFreeInvariants.put(heap, freeInv);
                    }
                }
                ImmutableList<Term> newLocalIns = tb.var(MiscTools.getLocalIns(loop, services));
                ImmutableList<Term> newLocalOuts = tb.var(MiscTools.getLocalOuts(loop, services));
                final LoopSpecification newInv = spec.create(loop, frame.getProgramMethod(),
                        frame.getProgramMethod().getContainerType(), newInvariants,
                        newFreeInvariants, newMods, newInfFlowSpecs, newVariant, selfTerm,
                        newLocalIns, newLocalOuts, atPres);
                services.getSpecificationRepository().addLoopInvariant(newInv);
            }
        }
        return selfTerm;
    }

    private void updateMergeContracts(final ImmutableSet<MergePointStatement> mpss,
            Map<LocationVariable, Term> atPres, Services services) {
        for (MergePointStatement mps : mpss) {
            ImmutableSet<MergeContract> mergeContracts
                    = services.getSpecificationRepository().getMergeContracts(mps);

            if(mergeContracts.size() != 1) {
                throw new IllegalArgumentException(
                        "Expected exactly one merge contract, got: " + mergeContracts.size());
            }

            MergeContract spec = mergeContracts.iterator().next();

            assert (spec instanceof UnparameterizedMergeContract
                    || spec instanceof PredicateAbstractionMergeContract)
                : "Unsupported kind of merge contract: " + spec.getClass().getSimpleName();

            if (spec instanceof PredicateAbstractionMergeContract) {
                final PredicateAbstractionMergeContract pamc
                        = (PredicateAbstractionMergeContract) spec;
                services.getSpecificationRepository().removeMergeContracts(mps);
                services.getSpecificationRepository()
                        .addMergeContract(new PredicateAbstractionMergeContract(mps, atPres,
                                pamc.getKJT(), pamc.getLatticeTypeName(),
                                pamc.getAbstractionPredicates(atPres, services)));
            }
        }
    }

    private static void updateBlockOrLoopContract(JavaStatement statement,
            AuxiliaryContract contract,
            final AuxiliaryContract.Variables newVariables,
            final Map<LocationVariable, Term> newPreconditions,
            final Map<LocationVariable, Term> newFreePreconditions,
            final Map<LocationVariable, Term> newPostconditions,
            final Map<LocationVariable, Term> newFreePostconditions,
            final Map<LocationVariable, Term> newModifiesClauses, Services services) {
        if (contract instanceof BlockContract) {
            final BlockContract newBlockContract
                    = ((BlockContract) contract).update((StatementBlock) statement,
                            newPreconditions, newFreePreconditions,
                            newPostconditions, newFreePostconditions,
                            newModifiesClauses, contract.getInfFlowSpecs(), newVariables,
                            contract.getMby(newVariables, services));

            services.getSpecificationRepository().removeBlockContract((BlockContract) contract);
            services.getSpecificationRepository().addBlockContract(newBlockContract, false);
        } else if (contract instanceof LoopContract) {
            final LoopContract newLoopContract;

            if (statement instanceof StatementBlock) {
                newLoopContract
                        = ((LoopContract) contract).update((StatementBlock) statement,
                                newPreconditions, newFreePreconditions,
                                newPostconditions, newFreePostconditions,
                                newModifiesClauses, contract.getInfFlowSpecs(), newVariables,
                                contract.getMby(newVariables, services),
                                ((LoopContract) contract).getDecreases(newVariables, services));
            } else {
                newLoopContract
                        = ((LoopContract) contract).update((LoopStatement) statement,
                                newPreconditions, newFreePreconditions,
                                newPostconditions, newFreePostconditions,
                                newModifiesClauses, contract.getInfFlowSpecs(), newVariables,
                                contract.getMby(newVariables, services),
                                ((LoopContract) contract).getDecreases(newVariables, services));
            }

            services.getSpecificationRepository().removeLoopContract((LoopContract) contract);
            services.getSpecificationRepository().addLoopContract(newLoopContract, false);
        }
    }
}
