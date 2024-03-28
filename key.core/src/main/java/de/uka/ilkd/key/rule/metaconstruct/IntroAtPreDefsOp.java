/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.*;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import static de.uka.ilkd.key.logic.equality.IrrelevantTermLabelsProperty.IRRELEVANT_TERM_LABELS_PROPERTY;

/**
 * Transformer that introduces concrete prestate variables
 */
public final class IntroAtPreDefsOp extends AbstractTermTransformer {

    /**
     * Comparator to use when sorting LocationVariables
     */
    private static final Comparator<LocationVariable> LOCVAR_COMPARATOR =
        Comparator.comparing(LocationVariable::name);

    public IntroAtPreDefsOp() {
        super(new Name("#introAtPreDefs"), 1);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Term target = term.sub(0);

        final ProgramElement pe = target.javaBlock().program();
        assert pe != null;

        final MethodFrame frame = JavaTools.getInnermostMethodFrame(pe, services);

        final PrestateVariablesUpdater updater = new PrestateVariablesUpdater(frame, services, tb);
        updater.addNeededHeaps(services.getTypeConverter().getHeapLDT().getAllHeaps().toList());
        updater.start();

        return tb.apply(updater.atPreUpdate, target, null);
    }

    /**
     * Replace the placeholder variables (see {@link AuxiliaryContract#getPlaceholderVariables()})
     * of all block contracts for blocks in {@code blocks} by {@code atPreVars} and
     * {@code atPreHeapVars}
     *
     * @param statements the blocks and loops whose contracts to update.
     * @param atPreVars all remembrance variables.
     * @param atPreHeapVars all remembrance heaps.
     * @param services services.
     */
    public void updateBlockAndLoopContracts(final ImmutableSet<? extends JavaStatement> statements,
            Map<LocationVariable, LocationVariable> atPreVars,
            Map<LocationVariable, LocationVariable> atPreHeapVars, Services services) {
        for (JavaStatement statement : statements) {
            ImmutableSet<AuxiliaryContract> contracts = DefaultImmutableSet.nil();

            if (statement instanceof StatementBlock block) {

                contracts =
                    contracts.union(services.getSpecificationRepository().getBlockContracts(block));
                contracts =
                    contracts.union(services.getSpecificationRepository().getLoopContracts(block));
            } else {
                LoopStatement loop = (LoopStatement) statement;
                contracts =
                    contracts.union(services.getSpecificationRepository().getLoopContracts(loop));
            }

            for (AuxiliaryContract contract : contracts) {
                Map<LocationVariable, LocationVariable> nonHeapVars =
                    new LinkedHashMap<>(atPreVars);
                atPreHeapVars.forEach((key, val) -> nonHeapVars.remove(key));
                atPreHeapVars.remove(services.getTypeConverter().getHeapLDT().getSavedHeap());

                final AuxiliaryContract.Variables variables = contract.getPlaceholderVariables();
                updateAuxiliaryContract(contract, statement, variables, nonHeapVars, atPreHeapVars,
                    services);
            }
        }
    }

    private static class PrestateVariablesUpdater extends JavaASTVisitor {
        /**
         * method frame for which prestate variables get introduced.
         */
        private final MethodFrame frame;
        /**
         * method name for which prestate variables get introduced.
         */
        private final String methodName;
        /**
         * The Term for {@code this} of the methodframe.
         */
        private final Term selfTerm;
        /**
         * A TermBuilder
         */
        private final TermBuilder tb;
        /**
         * renamings Term form.
         */
        private final Map<LocationVariable, Term> atPres = new LinkedHashMap<>();
        /**
         * renamings LocationVariable form.
         */
        private final Map<LocationVariable, LocationVariable> atPreVars = new LinkedHashMap<>();
        /**
         * heap renamings
         */
        private final Map<LocationVariable, LocationVariable> atPreHeapVars = new LinkedHashMap<>();
        /**
         * update Term for the prestate variables. Will get completed as the visitor runs.
         */
        private Term atPreUpdate;

        public PrestateVariablesUpdater(final MethodFrame frame, final Services services,
                final TermBuilder tb) {
            super(frame, services);
            this.frame = frame;
            selfTerm = MiscTools.getSelfTerm(frame, services);
            this.methodName = frame.getProgramMethod().getName();
            this.tb = tb;
            this.atPreUpdate = tb.skip();
        }

        @Override
        protected void doDefaultAction(final SourceElement node) {
            // ignore
        }

        @Override
        public void performActionOnBlockContract(final BlockContract contract) {
            performActionOnAuxContract(contract, contract.getBlock());
        }

        @Override
        public void performActionOnLoopContract(final LoopContract contract) {
            performActionOnAuxContract(contract,
                contract.isOnBlock() ? contract.getBlock() : contract.getLoop());
        }

        @Override
        public void performActionOnMergeContract(final MergeContract spec) {
            if ((!(spec instanceof UnparameterizedMergeContract)
                    && !(spec instanceof PredicateAbstractionMergeContract))) {
                throw new AssertionError(
                    "Unsupported kind of merge contract: " + spec.getClass().getSimpleName());
            }

            if (spec instanceof PredicateAbstractionMergeContract pamc) {
                final MergePointStatement mps = spec.getMergePointStatement();
                addNeededVariables(pamc.getAtPres().keySet());
                services.getSpecificationRepository().removeMergeContracts(mps);
                services.getSpecificationRepository()
                        .addMergeContract(new PredicateAbstractionMergeContract(mps, atPres,
                            pamc.getKJT(), pamc.getLatticeTypeName(),
                            pamc.getAbstractionPredicates(atPres, services)));
            }
        }

        @Override
        public void performActionOnJmlAssert(final JmlAssert x) {
            handleJmlStatement(x);
        }

        @Override
        public void performActionOnSetStatement(SetStatement x) {
            handleJmlStatement(x);
        }

        private void handleJmlStatement(Statement x) {
            var spec =
                Objects.requireNonNull(services.getSpecificationRepository().getStatementSpec(x));
            addNeededVariables(spec.vars().atPres.keySet());
            var newSpec = spec.updateVariables(atPres, services);
            services.getSpecificationRepository().addStatementSpec(x, newSpec);
        }

        @Override
        public void performActionOnLoopInvariant(final LoopSpecification spec) {
            addNeededVariables(spec.getInternalAtPres().keySet());
            Term self = selfTerm;
            if (spec.getInternalSelfTerm() == null) {
                // we're calling a static method from an instance context
                self = null;
            }
            final Term newVariant = spec.getVariant(self, atPres, services);
            Map<LocationVariable, Term> newMods = new LinkedHashMap<>();
            Map<LocationVariable, Term> newFreeMods = new LinkedHashMap<>();
            Map<LocationVariable, ImmutableList<InfFlowSpec>> newInfFlowSpecs =
                new LinkedHashMap<>();
            Map<LocationVariable, Term> newInvariants = new LinkedHashMap<>();
            Map<LocationVariable, Term> newFreeInvariants = new LinkedHashMap<>();
            for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                final Term term = spec.getInternalModifies().getOrDefault(
                    services.getTypeConverter().getHeapLDT().getHeap(), tb.allLocs());
                final Term freeTerm = spec.getInternalFreeModifies().getOrDefault(
                    services.getTypeConverter().getHeapLDT().getHeap(), tb.strictlyNothing());
                if (heap != services.getTypeConverter().getHeapLDT().getSavedHeap()
                        || !tb.strictlyNothing().equalsModProperty(term,
                            IRRELEVANT_TERM_LABELS_PROPERTY)) {
                    final Term m = spec.getModifies(heap, self, atPres, services);
                    final ImmutableList<InfFlowSpec> infFlowSpecs =
                        spec.getInfFlowSpecs(heap, self, atPres, services);
                    final Term inv = spec.getInvariant(heap, self, atPres, services);
                    if (inv != null) {
                        newInvariants.put(heap, inv);
                    }
                    if (m != null) {
                        newMods.put(heap, m);
                    }
                    newInfFlowSpecs.put(heap, infFlowSpecs);
                }
                if (heap != services.getTypeConverter().getHeapLDT().getSavedHeap()
                        || !tb.strictlyNothing().equalsModProperty(
                            freeTerm, IRRELEVANT_TERM_LABELS_PROPERTY)) {
                    final Term m = spec.getFreeModifies(heap, selfTerm, atPres, services);
                    final ImmutableList<InfFlowSpec> infFlowSpecs =
                        spec.getInfFlowSpecs(heap, selfTerm, atPres, services);
                    final Term freeInv = spec.getFreeInvariant(heap, self, atPres, services);
                    if (freeInv != null) {
                        newFreeInvariants.put(heap, freeInv);
                    }
                    if (m != null) {
                        newFreeMods.put(heap, m);
                    }
                    newInfFlowSpecs.put(heap, infFlowSpecs);
                }

            }
            final LoopStatement loop = spec.getLoop();
            ImmutableList<Term> newLocalIns = tb.var(MiscTools.getLocalIns(loop, services));
            ImmutableList<Term> newLocalOuts = tb.var(MiscTools.getLocalOuts(loop, services));
            final LoopSpecification newInv = spec.create(loop, frame.getProgramMethod(),
                frame.getProgramMethod().getContainerType(), newInvariants, newFreeInvariants,
                newMods, newFreeMods, newInfFlowSpecs, newVariant, self, newLocalIns,
                newLocalOuts, atPres);
            services.getSpecificationRepository().addLoopInvariant(newInv);
        }

        public void addNeededVariables(Collection<LocationVariable> variables) {
            List<LocationVariable> vars = new ArrayList<>(variables);
            vars.sort(LOCVAR_COMPARATOR);
            for (LocationVariable var : vars) {

                if (atPres.containsKey(var)) {
                    continue;
                }
                final LocationVariable l = tb.locationVariable(var.name() + "Before_" + methodName,
                    var.getKeYJavaType(), true);
                services.getNamespaces().programVariables().addSafely(l);

                final Term u = tb.elementary(l, tb.var(var));
                atPreUpdate = tb.parallel(atPreUpdate, u);

                atPres.put(var, tb.var(l));
                atPreVars.put(var, l);
            }
        }

        public void addNeededHeaps(Collection<LocationVariable> heapVariables) {
            List<LocationVariable> vars = new ArrayList<>(heapVariables);
            vars.sort(LOCVAR_COMPARATOR);
            for (LocationVariable var : vars) {
                if (atPres.containsKey(var)) {
                    continue;
                }
                final LocationVariable l =
                    tb.locationVariable(var.name() + "Before_" + methodName, var.sort(), true);
                services.getNamespaces().programVariables().addSafely(l);

                final Term u = tb.elementary(l, tb.var(var));
                atPreUpdate = tb.parallel(atPreUpdate, u);

                atPres.put(var, tb.var(l));
                atPreVars.put(var, l);
                atPreHeapVars.put(var, l);
            }
        }

        private void performActionOnAuxContract(final AuxiliaryContract contract,
                final JavaStatement statement) {
            final AuxiliaryContract.Variables variables = contract.getPlaceholderVariables();
            addNeededVariables(variables.outerRemembranceVariables.keySet());
            addNeededHeaps(variables.outerRemembranceHeaps.keySet());

            Map<LocationVariable, LocationVariable> nonHeapVars = new LinkedHashMap<>(atPreVars);
            atPreHeapVars.forEach((key, val) -> nonHeapVars.remove(key));
            // why does the saved heap get removed here?
            atPreHeapVars.remove(services.getTypeConverter().getHeapLDT().getSavedHeap());

            updateAuxiliaryContract(contract, statement, variables, nonHeapVars, atPreHeapVars,
                services);
        }
    }

    private static void updateAuxiliaryContract(final AuxiliaryContract contract,
            final JavaStatement statement, final AuxiliaryContract.Variables variables,
            final Map<LocationVariable, LocationVariable> nonHeapVars,
            final Map<LocationVariable, LocationVariable> atPreHeapVars, final Services services) {
        final AuxiliaryContract.Variables newVariables = new AuxiliaryContract.Variables(
            variables.self, variables.breakFlags, variables.continueFlags, variables.returnFlag,
            variables.result, variables.exception, variables.remembranceHeaps,
            variables.remembranceLocalVariables, atPreHeapVars, nonHeapVars, services);
        final Map<LocationVariable, Term> newPreconditions = new LinkedHashMap<>();
        final Map<LocationVariable, Term> newFreePreconditions = new LinkedHashMap<>();
        final Map<LocationVariable, Term> newPostconditions = new LinkedHashMap<>();
        final Map<LocationVariable, Term> newFreePostconditions = new LinkedHashMap<>();
        final Map<LocationVariable, Term> newModifiesClauses = new LinkedHashMap<>();
        final Map<LocationVariable, Term> newFreeModifiesClauses = new LinkedHashMap<>();

        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            // why does the saved heap just get ignored here?
            if (heap.name().equals(HeapLDT.SAVED_HEAP_NAME)) {
                continue;
            }

            newPreconditions.put(heap, contract.getPrecondition(heap, newVariables, services));
            newFreePreconditions.put(heap,
                contract.getFreePrecondition(heap, newVariables, services));
            newPostconditions.put(heap, contract.getPostcondition(heap, newVariables, services));
            newFreePostconditions.put(heap,
                contract.getFreePostcondition(heap, newVariables, services));
            newModifiesClauses.put(heap,
                contract.getModifiesClause(heap, newVariables.self, services));
            newFreeModifiesClauses.put(heap,
                contract.getFreeModifiesClause(heap, newVariables.self, services));
        }
        if (contract instanceof BlockContract) {
            final BlockContract newBlockContract = ((BlockContract) contract).update(
                (StatementBlock) statement, newPreconditions, newFreePreconditions,
                newPostconditions, newFreePostconditions,
                newModifiesClauses, newFreeModifiesClauses,
                contract.getInfFlowSpecs(), newVariables, contract.getMby(newVariables, services));

            services.getSpecificationRepository().removeBlockContract((BlockContract) contract);
            services.getSpecificationRepository().addBlockContract(newBlockContract, false);
        } else if (contract instanceof LoopContract) {
            final LoopContract newLoopContract;

            if (statement instanceof StatementBlock) {
                newLoopContract = ((LoopContract) contract).update((StatementBlock) statement,
                    newPreconditions, newFreePreconditions, newPostconditions,
                    newFreePostconditions, newModifiesClauses,
                    newFreeModifiesClauses, contract.getInfFlowSpecs(),
                    newVariables, contract.getMby(newVariables, services),
                    ((LoopContract) contract).getDecreases(newVariables, services));
            } else {
                newLoopContract = ((LoopContract) contract).update((LoopStatement) statement,
                    newPreconditions, newFreePreconditions, newPostconditions,
                    newFreePostconditions, newModifiesClauses, newFreeModifiesClauses,
                    contract.getInfFlowSpecs(), newVariables,
                    contract.getMby(newVariables, services),
                    ((LoopContract) contract).getDecreases(newVariables, services));
            }

            services.getSpecificationRepository().removeLoopContract((LoopContract) contract);
            services.getSpecificationRepository().addLoopContract(newLoopContract, false);
        }
    }
}
