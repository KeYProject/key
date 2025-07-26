/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.WhileInvariantTransformer;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Modality;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.RuleAbortException;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.*;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.logic.equality.IrrelevantTermLabelsProperty.IRRELEVANT_TERM_LABELS_PROPERTY;

@NullMarked
public class WhileInvariantRule implements BuiltInRule {
    /**
     * The hint used to refactor the initial invariant.
     */
    public static final String INITIAL_INVARIANT_ONLY_HINT = "onlyInitialInvariant";

    /**
     * The unit used to refactor the full invariant.
     */
    public static final String FULL_INVARIANT_TERM_HINT = "fullInvariant";

    public static final WhileInvariantRule INSTANCE = new WhileInvariantRule();

    private static final Name NAME = new Name("Loop Invariant");

    public static final String BODY_PRESERVES_INVARIANT_LABEL = "Body Preserves Invariant";

    protected WhileInvariantRule() {
    }

    // focus must be top level succedent
    @Override
    public boolean isApplicable(Goal goal, @Nullable PosInOccurrence pio) {
        if (pio == null || !pio.isTopLevel() || pio.isInAntec()) {
            return false;
        }
        // abort if inside of transformer
        if (Transformer.inTransformer(pio)) {
            return false;
        }
        Pair<JTerm, JTerm> up = applyUpdates((JTerm) pio.subTerm(), goal.proof().getServices());
        final JTerm progPost = up.second;
        if (!checkFocus(progPost)) {
            return false;
        }
        // active statement must be while loop
        final SourceElement activeStatement = JavaTools.getActiveStatement(progPost.javaBlock());
        return activeStatement instanceof While;
    }

    private static boolean checkFocus(final JTerm progPost) {
        // focus (below update) must be modality term
        return progPost.op() instanceof JModality;
    }

    static Pair<JTerm, JTerm> applyUpdates(JTerm focusTerm, TermServices services) {
        if (focusTerm.op() instanceof UpdateApplication) {
            return new Pair<>(UpdateApplication.getUpdate(focusTerm),
                UpdateApplication.getTarget(focusTerm));
        } else {
            return new Pair<>(services.getTermBuilder().skip(), focusTerm);
        }
    }


    @Override
    public @NonNull ImmutableList<Goal> apply(Goal goal, final RuleApp ruleApp)
            throws RuleAbortException {
        return new WhileInvariantRuleApplier(goal, (LoopInvariantBuiltInRuleApp<?>) ruleApp)
                .apply();
    }


    @Override
    public Name name() {
        return NAME;
    }


    @Override
    public String displayName() {
        return toString();
    }


    @Override
    public String toString() {
        return NAME.toString();
    }


    @Override
    public LoopInvariantBuiltInRuleApp<?> createApp(PosInOccurrence pos, TermServices services) {
        return new LoopInvariantBuiltInRuleApp<>(this, pos, services);
    }

    /**
     * @param u The update term.
     * @param progPost The program's post condition.
     * @param loop The while loop.
     * @param inv The invariant's loop specification.
     * @param selfTerm The term for the self variable.
     * @param innermostExecutionContext The innermost execution context.
     */
    public record Instantiation(JTerm u, JTerm progPost, While loop, LoopSpecification inv,
            JTerm selfTerm,
            ExecutionContext innermostExecutionContext) {
        public Instantiation {
            assert u != null;
            assert u.sort() == JavaDLTheory.UPDATE;
            assert progPost != null;
            assert progPost.sort() == JavaDLTheory.FORMULA;
            assert loop != null;
            assert inv != null;
        }
    }

    public record AnonUpdateData(JTerm anonUpdate, JTerm loopHeap, JTerm loopHeapAtPre,
            JTerm anonHeap) {
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    protected static class WhileInvariantRuleApplier {
        protected final Goal goal;
        protected final LoopInvariantBuiltInRuleApp ruleApp;
        protected final TermLabelState termLabelState;
        protected final Services services;
        protected final KeYJavaType booleanKJT;
        protected final TermBuilder tb;
        protected final Sequent applicationSequent;
        protected final Map<LocationVariable, JTerm> atPres;
        protected final List<LocationVariable> heapContext;
        protected final JTerm invTerm;
        protected final JTerm invFreeTerm;
        protected final JTerm[] uAnon;
        protected final JTerm[] uBeforeLoopDefAnonVariant;
        protected final JTerm uAnonInv;
        protected final Instantiation inst;
        protected final Guard guardStuff;
        protected final JavaBlock guardJb;
        protected final JTerm guardTrueTerm;
        protected final JTerm guardFalseTerm;
        protected final Pair<JTerm, JTerm> variantPair;
        protected final JTerm variantUpdate;
        protected final JTerm variantPO;
        protected final JTerm strictlyNothing;
        protected final LocationVariable permissionHeap;
        protected final ImmutableList<AnonUpdateData> anonUpdateDatas;
        protected final ImmutableSet<LocationVariable> localIns;
        protected JTerm anonUpdate;
        protected final ImmutableSet<LocationVariable> localOuts;
        protected JTerm beforeLoopUpdate;
        protected final Map<LocationVariable, Map<JTerm, JTerm>> heapToBeforeLoop =
            new LinkedHashMap<>();
        protected JTerm wellFormedAnon = null;
        protected JTerm frameCondition = null;
        protected JTerm reachableState = null;
        protected JTerm anonHeap = null;
        protected final JTerm localAnonUpdate;


        public WhileInvariantRuleApplier(Goal goal, LoopInvariantBuiltInRuleApp ruleApp) {
            this.goal = goal;
            this.ruleApp = ruleApp;
            termLabelState = new TermLabelState();
            applicationSequent = goal.sequent();
            services = goal.getOverlayServices();
            booleanKJT = services.getTypeConverter().getBooleanType();
            tb = services.getTermBuilder();
            strictlyNothing = tb.strictlyNothing();

            // get instantiation
            inst = instantiate(ruleApp, services);

            atPres = inst.inv.getInternalAtPres();
            heapContext = ((IBuiltInRuleApp) ruleApp).getHeapContext();

            invTerm = conjunctInv(services, inst, atPres, heapContext);
            invFreeTerm = conjunctFreeInv(services, inst, atPres, heapContext);
            final Map<LocationVariable, JTerm> modifiables = new LinkedHashMap<>();
            final Map<LocationVariable, JTerm> freeModifiables = new LinkedHashMap<>();
            for (LocationVariable heap : heapContext) {
                modifiables.put(heap,
                    inst.inv.getModifiable(heap, inst.selfTerm, atPres, services));
                freeModifiables.put(heap,
                    inst.inv.getFreeModifiable(heap, inst.selfTerm, atPres, services));
            }

            final JTerm variant = inst.inv.getVariant(inst.selfTerm, atPres, services);

            // collect input and output local variables,
            // prepare reachableIn and reachableOut
            final ImmutableSet<LocationVariable> localIns =
                MiscTools.getLocalIns(inst.loop, services);
            final ImmutableSet<LocationVariable> localOuts =
                MiscTools.getLocalOuts(inst.loop, services);
            JTerm reachableIn = tb.tt();
            for (var pv : localIns) {
                reachableIn = tb.and(reachableIn, tb.reachableValue(pv));
            }
            JTerm reachableOut = tb.tt();

            for (var pv : localOuts) {
                reachableOut = tb.and(reachableOut, tb.reachableValue(pv));
            }

            // prepare variant
            variantPair = prepareVariant(inst, variant, services);
            variantUpdate = variantPair.first;
            variantPO = variantPair.second;

            // prepare guard
            guardStuff = prepareGuard(inst, booleanKJT, ruleApp, services);
            guardJb = guardStuff.javaBlock;
            guardTrueTerm = guardStuff.trueTerm;
            guardFalseTerm = guardStuff.falseTerm;

            for (LocationVariable heap : heapContext) {
                heapToBeforeLoop.put(heap, new LinkedHashMap<>());
                final LocationVariable lv =
                    tb.locationVariable(heap + "Before_LOOP", heap.sort(), true);
                services.getNamespaces().programVariables().addSafely(lv);
                final JTerm u = tb.elementary(lv, tb.var(heap));
                if (beforeLoopUpdate == null) {
                    beforeLoopUpdate = u;
                } else {
                    beforeLoopUpdate = tb.parallel(beforeLoopUpdate, u);
                }
                heapToBeforeLoop.get(heap).put(tb.var(heap), tb.var(lv));
            }

            // This is needed because of the shallow access of \permission,
            // heap references that are deeper than top-level have to be replaced to, but with
            // heapBefore_....
            permissionHeap = services.getTypeConverter().getHeapLDT().getPermissionHeap();

            if (permissionHeap != null && heapContext.contains(permissionHeap)) {
                final LocationVariable baseHeap =
                    services.getTypeConverter().getHeapLDT().getHeap();
                final JTerm baseHeapVar = services.getTermBuilder().var(baseHeap);
                heapToBeforeLoop.get(permissionHeap).put(baseHeapVar,
                    heapToBeforeLoop.get(baseHeap).get(baseHeapVar));
            }

            for (ProgramVariable pv : localOuts) {
                final String pvBeforeLoopName = tb.newName(pv.name() + "Before_LOOP");
                final LocationVariable pvBeforeLoop =
                    new LocationVariable(new ProgramElementName(pvBeforeLoopName),
                        pv.getKeYJavaType());
                services.getNamespaces().programVariables().addSafely(pvBeforeLoop);
                beforeLoopUpdate =
                    tb.parallel(beforeLoopUpdate, tb.elementary(pvBeforeLoop, tb.var(pv)));
                heapToBeforeLoop.get(services.getTypeConverter().getHeapLDT().getHeap()).put(
                    tb.var(pv),
                    tb.var(pvBeforeLoop));
            }

            // prepare anon update, frame condition, etc.
            var anonUpdate = createLocalAnonUpdate(localOuts, services);
            localAnonUpdate = anonUpdate != null ? anonUpdate : tb.skip();
            // Term anonAssumption = null;
            ImmutableList<AnonUpdateData> anonUpdateDatas = ImmutableSLList.nil();
            for (LocationVariable heap : heapContext) {
                final AnonUpdateData tAnon =
                    createAnonUpdate(heap, modifiables.get(heap), inst.inv, services);
                anonUpdateDatas = anonUpdateDatas.append(tAnon);
                if (anonUpdate == null) {
                    anonUpdate = tAnon.anonUpdate;
                } else {
                    anonUpdate = tb.parallel(anonUpdate, tAnon.anonUpdate);
                }
                if (wellFormedAnon == null) {
                    wellFormedAnon = tb.wellFormed(tAnon.anonHeap);
                } else {
                    wellFormedAnon = tb.and(wellFormedAnon, tb.wellFormed(tAnon.anonHeap));
                }
                if (anonHeap == null) {
                    anonHeap = tAnon.anonHeap;
                }

                var modifiable = modifiables.get(heap);
                var freeModifiable = freeModifiables.get(heap);

                final JTerm currentFrame;
                if (strictlyNothing.equalsModProperty(
                    modifiable, IRRELEVANT_TERM_LABELS_PROPERTY)) {
                    if (strictlyNothing.equalsModProperty(
                        freeModifiable, IRRELEVANT_TERM_LABELS_PROPERTY)) {
                        currentFrame =
                            tb.frameStrictlyEmpty(tb.var(heap), heapToBeforeLoop.get(heap));
                    } else {
                        currentFrame =
                            tb.frame(tb.var(heap), heapToBeforeLoop.get(heap), freeModifiable);
                    }
                } else {
                    if (strictlyNothing.equalsModProperty(
                        freeModifiable, IRRELEVANT_TERM_LABELS_PROPERTY)) {
                        currentFrame =
                            tb.frame(tb.var(heap), heapToBeforeLoop.get(heap), modifiable);
                    } else {
                        currentFrame = tb.frame(
                            tb.var(heap), heapToBeforeLoop.get(heap),
                            tb.union(modifiable, freeModifiable));
                    }
                }
                if (frameCondition == null) {
                    frameCondition = currentFrame;
                } else {
                    frameCondition = tb.and(frameCondition, currentFrame);
                }
                if (reachableState == null) {
                    reachableState = tb.wellFormed(heap);
                } else {
                    reachableState = tb.and(reachableState, tb.wellFormed(heap));
                }
            }

            // prepare common assumption
            uAnon = new JTerm[] { inst.u, anonUpdate };
            uBeforeLoopDefAnonVariant =
                new JTerm[] { inst.u, beforeLoopUpdate, anonUpdate, variantUpdate };
            uAnonInv =
                tb.applySequential(uAnon, tb.and(tb.and(invTerm, reachableOut), invFreeTerm));

            this.anonUpdateDatas = anonUpdateDatas;
            this.anonUpdate = anonUpdate;
            this.localOuts = localOuts;
            this.localIns = localIns;
        }

        public @NonNull ImmutableList<Goal> apply() {
            final ImmutableList<Goal> result = goal.split(3);
            prepareGoals(result);
            return result;
        }

        protected void prepareGoals(ImmutableList<Goal> result) {
            Goal initGoal = result.get(0);
            Goal preserveGoal = result.get(1);
            Goal useGoal = result.get(2);

            prepareInvInitiallyValidBranch(initGoal);
            prepareBodyPreservesBranch(preserveGoal);
            prepareUseCaseBranch(useGoal);
        }


        public static Instantiation instantiate(final LoopInvariantBuiltInRuleApp<?> app,
                Services services) throws RuleAbortException {
            final JTerm focusTerm = (JTerm) app.posInOccurrence().subTerm();

            // leading update?
            final Pair<JTerm, JTerm> update = applyUpdates(focusTerm, services);
            final JTerm u = update.first;
            final JTerm progPost = update.second;

            // focus (below update) must be modality term
            if (!checkFocus(progPost)) {
                return null;
            }

            // active statement must be while loop
            final While loop = app.getLoopStatement();

            // try to get invariant from JML specification
            LoopSpecification spec = app.getSpec();
            if (spec == null) {
                throw new RuleAbortException("no invariant found");
            }

            // collect self, execution context
            final MethodFrame innermostMethodFrame =
                JavaTools.getInnermostMethodFrame(progPost.javaBlock(), services);
            if (innermostMethodFrame != null) {
                spec = spec.setTarget(innermostMethodFrame.getProgramMethod());
            }

            final JTerm selfTerm = innermostMethodFrame == null ? null
                    : MiscTools.getSelfTerm(innermostMethodFrame, services);

            final ExecutionContext innermostExecutionContext = innermostMethodFrame == null ? null
                    : (ExecutionContext) innermostMethodFrame.getExecutionContext();
            services.getSpecificationRepository().addLoopInvariant(spec);

            // cache and return result
            return new Instantiation(u, progPost, loop, spec, selfTerm, innermostExecutionContext);
        }

        private static JTerm createLocalAnonUpdate(ImmutableSet<LocationVariable> localOuts,
                Services services) {
            JTerm anonUpdate = null;
            final TermBuilder tb = services.getTermBuilder();
            for (LocationVariable pv : localOuts) {
                final Name anonFuncName = new Name(tb.newName(pv.name().toString()));
                final Function anonFunc = new JFunction(anonFuncName, pv.sort(), true);
                services.getNamespaces().functions().addSafely(anonFunc);
                final JTerm elemUpd = tb.elementary(pv, tb.func(anonFunc));
                if (anonUpdate == null) {
                    anonUpdate = elemUpd;
                } else {
                    anonUpdate = tb.parallel(anonUpdate, elemUpd);
                }
            }
            return anonUpdate;
        }

        /**
         * @return (assumption, anon update, anon heap)
         */
        private static AnonUpdateData createAnonUpdate(LocationVariable heap, JTerm modifiable,
                LoopSpecification inv, Services services) {
            final TermBuilder tb = services.getTermBuilder();
            final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
            final Name loopHeapName = new Name(tb.newName(heap + "_After_LOOP"));
            final Function loopHeapFunc =
                new JFunction(loopHeapName, heapLDT.targetSort(), true);
            services.getNamespaces().functions().addSafely(loopHeapFunc);

            final JTerm loopHeap = tb.func(loopHeapFunc);
            final Name anonHeapName = new Name(tb.newName("anon_" + heap + "_LOOP"));
            final Function anonHeapFunc = new JFunction(anonHeapName, heap.sort());
            services.getNamespaces().functions().addSafely(anonHeapFunc);
            final JTerm anonHeapTerm =
                tb.label(tb.func(anonHeapFunc), ParameterlessTermLabel.ANON_HEAP_LABEL);

            // check for strictly pure loops
            final JTerm anonUpdate;
            if (tb.strictlyNothing().equalsModProperty(modifiable,
                IRRELEVANT_TERM_LABELS_PROPERTY)) {
                anonUpdate = tb.skip();
            } else {
                anonUpdate = tb.anonUpd(heap, modifiable, anonHeapTerm);
            }

            return new AnonUpdateData(anonUpdate, loopHeap, tb.getBaseHeap(), anonHeapTerm);
        }


        protected JTerm conjunctInv(Services services, Instantiation inst,
                final Map<LocationVariable, JTerm> atPres,
                final List<LocationVariable> heapContext) {
            JTerm invTerm = services.getTermBuilder().tt();
            for (LocationVariable heap : heapContext) {
                final JTerm i = inst.inv.getInvariant(heap, inst.selfTerm, atPres, services);
                if (i == null) {
                    continue;
                }
                if (invTerm == null) {
                    invTerm = i;
                } else {
                    invTerm = services.getTermBuilder().and(invTerm, i);
                }
            }
            return invTerm;
        }

        protected JTerm conjunctFreeInv(Services services, Instantiation inst,
                final Map<LocationVariable, JTerm> atPres,
                final List<LocationVariable> heapContext) {
            JTerm freeInvTerm = services.getTermBuilder().tt();
            for (LocationVariable heap : heapContext) {
                final JTerm i = inst.inv.getFreeInvariant(heap, inst.selfTerm, atPres, services);
                if (i == null) {
                    continue;
                }
                if (freeInvTerm == null) {
                    freeInvTerm = i;
                } else {
                    freeInvTerm = services.getTermBuilder().and(freeInvTerm, i);
                }
            }
            return freeInvTerm;
        }

        protected Pair<JTerm, JTerm> prepareVariant(Instantiation inst, JTerm variant,
                TermServices services) {
            final TermBuilder tb = services.getTermBuilder();
            final ProgramElementName variantName = new ProgramElementName(tb.newName("variant"));
            final LocationVariable variantPV = new LocationVariable(variantName, JavaDLTheory.ANY);
            services.getNamespaces().programVariables().addSafely(variantPV);

            Modality modality = ((Modality) inst.progPost.op());
            final boolean dia = modality.<JModality.JavaModalityKind>kind().terminationSensitive();
            final JTerm variantUpdate = dia ? tb.elementary(variantPV, variant) : tb.skip();
            final JTerm variantPO = dia ? tb.prec(variant, tb.var(variantPV)) : tb.tt();
            return new Pair<>(variantUpdate, variantPO);
        }


        protected JTerm bodyTerm(TermLabelState termLabelState, Services services,
                RuleApp ruleApp,
                final Sequent applicationSequent, Instantiation inst, final JTerm invTerm,
                JTerm frameCondition, final JTerm variantPO, Goal bodyGoal, final JavaBlock guardJb,
                final JTerm guardTrueTerm) {
            final WhileInvariantTransformer wir = new WhileInvariantTransformer();
            final TermBuilder tb = services.getTermBuilder();
            SVInstantiations svInst = SVInstantiations.EMPTY_SVINSTANTIATIONS.replace(null, null,
                inst.innermostExecutionContext, null, services);
            for (SchemaVariable sv : wir.neededInstantiations(inst.loop, svInst)) {
                assert sv instanceof ProgramSV;
                svInst =
                    svInst.addInteresting(sv, (Name) new ProgramElementName(sv.name().toString()),
                        services);
            }
            JTerm fullInvariant = tb.and(invTerm, frameCondition, variantPO);
            fullInvariant = TermLabelManager.refactorTerm(
                termLabelState, services, null, fullInvariant,
                ruleApp.rule(), bodyGoal, FULL_INVARIANT_TERM_HINT, null);

            JTerm bodyTerm = wir.transform(termLabelState, (Rule) ruleApp.rule(), ruleApp, bodyGoal,
                applicationSequent,
                ruleApp.posInOccurrence(), inst.progPost, fullInvariant, svInst, services);
            return tb.imp(tb.box(guardJb, guardTrueTerm), bodyTerm);
        }


        protected SequentFormula initFormula(TermLabelState termLabelState,
                Instantiation inst,
                final JTerm invTerm, JTerm reachableState, Services services, Goal initGoal) {
            final TermBuilder tb = services.getTermBuilder();
            JTerm sfTerm = tb.apply(inst.u, tb.and(invTerm, reachableState), null);
            sfTerm = TermLabelManager.refactorTerm(termLabelState, services, null, sfTerm,
                ruleApp.rule(),
                initGoal, INITIAL_INVARIANT_ONLY_HINT, null);
            return new SequentFormula(sfTerm);
        }

        protected JTerm useCaseFormula(TermLabelState termLabelState, Services services,
                RuleApp ruleApp,
                Instantiation inst, Goal useGoal, final JavaBlock guardJb,
                final JTerm guardFalseTerm) {
            final TermBuilder tb = services.getTermBuilder();
            JavaBlock useJavaBlock =
                JavaTools.removeActiveStatement(inst.progPost.javaBlock(), services);
            var modality = (Modality) inst.progPost.op();
            final ImmutableArray<TermLabel> instantiateLabels = TermLabelManager.instantiateLabels(
                termLabelState, services, ruleApp.posInOccurrence(), ruleApp.rule(), ruleApp,
                useGoal,
                "UseModality", null,
                tb.tf().createTerm(JModality.getModality(modality.kind(), useJavaBlock),
                    new ImmutableArray<>(inst.progPost.sub(0)),
                    null, inst.progPost.getLabels()));
            JTerm restPsi =
                tb.prog(modality.kind(), useJavaBlock, inst.progPost.sub(0),
                    instantiateLabels);
            return tb.box(guardJb, tb.imp(guardFalseTerm, restPsi));
        }

        protected Guard prepareGuard(final Instantiation inst,
                final KeYJavaType booleanKJT, LoopInvariantBuiltInRuleApp loopRuleApp,
                final TermServices services) {
            final TermBuilder tb = services.getTermBuilder();
            final ProgramElementName guardVarName = new ProgramElementName(tb.newName("b"));
            final LocationVariable guardVar = new LocationVariable(guardVarName, booleanKJT);
            services.getNamespaces().programVariables().addSafely(guardVar);
            loopRuleApp.setGuard(tb.var(guardVar));
            final VariableSpecification guardVarSpec =
                new VariableSpecification(guardVar, inst.loop.getGuardExpression(), booleanKJT);
            final LocalVariableDeclaration guardVarDecl =
                new LocalVariableDeclaration(new TypeRef(booleanKJT), guardVarSpec);
            final Statement guardVarMethodFrame =
                inst.innermostExecutionContext == null ? guardVarDecl
                        : new MethodFrame(null, inst.innermostExecutionContext,
                            new StatementBlock(guardVarDecl));
            final JavaBlock guardJb =
                JavaBlock.createJavaBlock(new StatementBlock(guardVarMethodFrame));
            final JTerm guardTrueTerm = tb.equals(tb.var(guardVar), tb.TRUE());
            final JTerm guardFalseTerm = tb.equals(tb.var(guardVar), tb.FALSE());
            return new Guard(guardJb, guardTrueTerm, guardFalseTerm);
        }

        /**
         * Represents a {@code javaBlock} which is executed if the {@code trueTerm} is true.
         *
         * @param javaBlock a block of java code
         * @param trueTerm a boolean term
         * @param falseTerm the negation (at least semantically) of {@code trueTerm}
         */
        protected record Guard(JavaBlock javaBlock, JTerm trueTerm, JTerm falseTerm) {
        }

        /// Creates the initially valid branch.
        /// ```
        /// "Invariant Initially Valid":
        /// \replacewith (==> inv );
        /// ```
        protected void prepareInvInitiallyValidBranch(Goal initGoal) {
            initGoal.setBranchLabel("Invariant Initially Valid");
            initGoal.changeFormula(
                initFormula(termLabelState, inst, invTerm, reachableState, services, initGoal),
                ruleApp.posInOccurrence());
            TermLabelManager.refactorGoal(termLabelState, services, ruleApp.posInOccurrence(),
                ruleApp.rule(),
                initGoal, null, null);
        }


        /// Creates the preservation branch:
        /// ```
        /// "Body Preserves Invariant":
        /// \replacewith (==> #atPreEqs(anon1)
        /// -> #introNewAnonUpdate(#modifiable,
        /// #locDepFunc(anon1,
        /// \[{.. while (#e)#s ...}\]post) & inv ->
        /// (\[{ method-frame(#ex){#typeof(#e)#v1 = #e;}}\]#v1=TRUE ->
        /// #whileInvRule(\[{.. while (#e)#s ...}\]post,
        /// #locDepFunc(anon1, \[{.. while (#e)#s ...}\]post)
        /// & inv)), anon1));
        /// ```
        protected void prepareBodyPreservesBranch(Goal bodyGoal) {
            final TermBuilder tb = services.getTermBuilder();
            bodyGoal.setBranchLabel(BODY_PRESERVES_INVARIANT_LABEL);
            bodyGoal.addFormula(new SequentFormula(wellFormedAnon), true, false);

            bodyGoal.addFormula(new SequentFormula(uAnonInv), true, false);

            JTerm guardTrueBody =
                bodyTerm(termLabelState, services, ruleApp, applicationSequent, inst,
                    invTerm, frameCondition, variantPO, bodyGoal, guardJb, guardTrueTerm);

            bodyGoal.changeFormula(
                new SequentFormula(tb.applySequential(uBeforeLoopDefAnonVariant, guardTrueBody)),
                ruleApp.posInOccurrence());
        }


        /// Creates the goal/brand "Use Case":
        ///
        /// ```"Use Case":
        /// \replacewith (==> #introNewAnonUpdate(#modifiable, inv ->
        /// (\[{ method-frame(#ex){#typeof(#e)#v1 = #e;}}\]
        /// (#v1=FALSE -> \[{.. ...}\]post)),anon2))
        /// ```
        protected void prepareUseCaseBranch(Goal useGoal) {
            useGoal.setBranchLabel("Use Case");
            useGoal.addFormula(new SequentFormula(wellFormedAnon), true, false);
            useGoal.addFormula(new SequentFormula(uAnonInv), true, false);
            final TermBuilder tb = services.getTermBuilder();

            JTerm guardFalseRestPsi =
                useCaseFormula(termLabelState, services, ruleApp, inst, useGoal,
                    guardJb, guardFalseTerm);
            useGoal.changeFormula(new SequentFormula(tb.applySequential(uAnon, guardFalseRestPsi)),
                ruleApp.posInOccurrence());
        }
    }
}
