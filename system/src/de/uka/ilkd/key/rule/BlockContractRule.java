package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.expression.operator.NotEquals;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.java.visitor.CreatingASTVisitor;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.java.visitor.OuterBreakContinueAndReturnReplacer;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.util.ExtList;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

import java.util.*;

public class BlockContractRule implements BuiltInRule {

    public static final BlockContractRule INSTANCE = new BlockContractRule();

    private static final Name NAME = new Name("Block Contract");
    private static final TermBuilder TB = TermBuilder.DF;

    public static Instantiation instantiate(final Term formula, final Services services) {
        final Pair<Term, Term> updateAndTarget = extractUpdate(formula);
        final Term update = updateAndTarget.first;
        final Term target = updateAndTarget.second;
        if (!(target.op() instanceof Modality)) {
            return null;
        }
        final Modality modality = (Modality) target.op();
        final StatementBlock block = getActiveBlock(modality, target.javaBlock(), services);
        if (block == null) {
            return null;
        }
        final MethodFrame frame = JavaTools.getInnermostMethodFrame(target.javaBlock(), services);
        final Term self = (frame == null ? null : MiscTools.getSelfTerm(frame, services));
        final ExecutionContext context = (frame == null ? null : (ExecutionContext) frame.getExecutionContext());
        return new Instantiation(update, target, modality, self, block, context);
    }

    private static Pair<Term, Term> extractUpdate(Term focusTerm) {
        if (focusTerm.op() instanceof UpdateApplication) {
            return new Pair<Term, Term>(UpdateApplication.getUpdate(focusTerm), UpdateApplication.getTarget(focusTerm));
        }
        else {
            return new Pair<Term, Term>(TB.skip(), focusTerm);
        }
    }

    // TODO Find better name.
    public static StatementBlock getActiveBlock(Modality modality, JavaBlock java, Services services) {
        // TODO Clean up.
        // get first block in prefix that has an applicable contract
        SourceElement element = java.program().getFirstElement();
        while ((element instanceof ProgramPrefix || element instanceof CatchAllStatement)
                && !(element instanceof StatementBlock && ((StatementBlock) element).isEmpty())) {
            if (element instanceof StatementBlock
                    && !getApplicableContracts(services.getSpecificationRepository(), (StatementBlock) element, modality).isEmpty()) {
                break;
            }
            if (element instanceof LabeledStatement) {
                element = ((LabeledStatement) element).getChildAt(1);
            }
            else if (element instanceof CatchAllStatement) {
                element = ((CatchAllStatement) element).getBody();
            }
            else if (element instanceof StatementContainer) {
                element = ((StatementContainer) element).getStatementAt(0);
            }
            else {
                element = element.getFirstElement();
            }
        }
        if (element instanceof StatementBlock) {
            return (StatementBlock) element;
        }
        return null;
    }

    public static ImmutableSet<BlockContract> getApplicableContracts(final Instantiation instantiation, final Services services) {
        if (instantiation == null) {
            return DefaultImmutableSet.<BlockContract>nil();
        }
        return getApplicableContracts(services.getSpecificationRepository(), instantiation.block, instantiation.modality);
    }

    private static ImmutableSet<BlockContract> getApplicableContracts(final SpecificationRepository specifications,
                                                                      final StatementBlock block,
                                                                      final Modality modality) {
        ImmutableSet<BlockContract> result = specifications.getBlockContracts(block, modality);
        if (modality == Modality.BOX) {
            result = result.union(specifications.getBlockContracts(block, Modality.DIA));
        }
        else if (modality == Modality.BOX_TRANSACTION) {
            result = result.union(specifications.getBlockContracts(block, Modality.DIA_TRANSACTION));
        }
        return result;
    }

    private Term lastFocusTerm;
    private Instantiation lastInstantiation;

    private BlockContractRule() {
    }

    @Override
    public boolean isApplicable(final Goal goal, final PosInOccurrence occurrence) {
        if (occurrence == null || !occurrence.isTopLevel() || occurrence.isInAntec()) {
            return false;
        }
        final Instantiation instantiation = instantiateAndCache(occurrence.subTerm(), goal.proof().getServices());
        if (instantiation == null) {
            return false;
        }
        final ImmutableSet<BlockContract> contracts = getApplicableContracts(instantiation, goal.proof().getServices());
        return !contracts.isEmpty();
    }

    @Override
    public ImmutableList<Goal> apply(final Goal goal, final Services services, final RuleApp application) throws RuleAbortException {
        assert application instanceof BlockContractBuiltInRuleApp;
        return apply(goal, services, (BlockContractBuiltInRuleApp) application);
    }

    public ImmutableList<Goal> apply(final Goal goal, final Services services, final BlockContractBuiltInRuleApp application) throws RuleAbortException {
        final Instantiation instantiation = instantiateAndCache(application.posInOccurrence().subTerm(), services);
        final BlockContract contract = application.getContract();
        //assert contract.getBlock().equals(instantiation.block);
        final IProgramMethod method = contract.getTarget();
        final Term contextUpdate = instantiation.update;

        final Map<Label, ProgramVariable> breakFlags = contract.getInternalBreakFlags();
        final Map<Label, ProgramVariable> continueFlags = contract.getInternalContinueFlags();
        final ProgramVariable returnFlag = contract.getInternalReturnFlag();

        final List<ProgramVariable> flags = createAndRegisterFlags(goal, breakFlags.values(), continueFlags.values(), returnFlag, services);
        final ProgramVariable resultVariable = createAndRegisterResultVariable(goal, method, services);
        final ProgramVariable exceptionVariable = createAndRegisterExceptionVariable(goal, method, services);

        final List<LocationVariable> heaps = HeapContext.getModHeaps(goal.proof().getServices(), instantiation.modality.transaction());
        // TODO Name atPreVars is not intuitive.
        Map<LocationVariable, LocationVariable> atPreVars = createAndRegisterAtPreVars(goal, heaps, services);
        final Map<LocationVariable, Term> atPres = HeapContext.getAtPres(atPreVars, services);

        final ImmutableSet<ProgramVariable> localInVariables = MiscTools.getLocalIns(instantiation.block, services);

        final Term precondition = generatePrecondition(heaps, contract, instantiation.self, TB.var(flags), atPres, services);
        final Term wellFormedHeapsCondition = generateWellFormedHeapsCondition(heaps, services);
        final Term reachableInCondition = generateReachableCondition(localInVariables, services);
        final Term[] preconditions = new Term[] {precondition, wellFormedHeapsCondition, reachableInCondition};

        final ImmutableSet<ProgramVariable> localOutVariables = MiscTools.getLocalOuts(instantiation.block, services);

        final Pair<Term, Map<LocationVariable, Map<Term, Term>>> remembranceUpdateAndVariables
                = generateRemembranceUpdateAndVariables(heaps, localOutVariables, services);
        final Term remembranceUpdate = remembranceUpdateAndVariables.first;
        final Map<LocationVariable, Map<Term, Term>> remembranceVariables = remembranceUpdateAndVariables.second;
        final Map<LocationVariable, Term> modifiesConditions = generateModifiesConditions(heaps, contract, instantiation.self, TB.var(flags), services);
        final Pair<Term, Term> anonymisationUpdateAndWellFormedAnonymisationHeapsCondition
                = generateAnonymisationUpdateAndWellFormedAnonymisationHeapsCondition(heaps, localOutVariables, modifiesConditions, services);
        final Term anonymisationUpdate = anonymisationUpdateAndWellFormedAnonymisationHeapsCondition.first;
        final Term postcondition = generatePostcondition(heaps, contract, instantiation.self, TB.var(flags), TB.var(resultVariable), TB.var(exceptionVariable), atPres, services);
        final Term frameCondition = generateFrameCondition(heaps, modifiesConditions, remembranceVariables, services);
        final Term atMostOneFlagSetCondition = generateAtMostOneFlagSetCondition(breakFlags, continueFlags, returnFlag, exceptionVariable, services);
        final Term wellFormedAnonymisationHeapsCondition = anonymisationUpdateAndWellFormedAnonymisationHeapsCondition.second;
        final Term reachableOutCondition = generateReachableCondition(localOutVariables, services);

        final ImmutableList<Goal> result = goal.split(3);
        setUpValidityGoal(result.tail().tail().head(),
                new Term[] {contextUpdate, remembranceUpdate},
                preconditions, instantiation,
                breakFlags, continueFlags, returnFlag, resultVariable, method.getReturnType(), exceptionVariable,
                new Term[] {postcondition, frameCondition/*, atMostOneFlagSetCondition*/},
                application.posInOccurrence(), services);
        setUpPreconditionGoal(result.tail().head(), contextUpdate, preconditions, application.posInOccurrence());
        setUpUsageGoal(result.head(), instantiation.block,
                new Term[] {contextUpdate, remembranceUpdate, anonymisationUpdate},
                new Term[] {postcondition, wellFormedAnonymisationHeapsCondition, reachableOutCondition, atMostOneFlagSetCondition},
                breakFlags, continueFlags, returnFlag, resultVariable, exceptionVariable,
                instantiation.formula, application.posInOccurrence(), services);

        return result;
    }

    private Instantiation instantiateAndCache(final Term focusTerm, final Services services) {
        if (focusTerm == lastFocusTerm) {
            return lastInstantiation;
        }
        else {
            final Instantiation result = instantiate(focusTerm, services);
            lastFocusTerm = focusTerm;
            lastInstantiation = result;
            return result;
        }
    }

    private List<ProgramVariable> createAndRegisterFlags(final Goal goal,
                                                         final Collection<ProgramVariable> breakFlags,
                                                         final Collection<ProgramVariable> continueFlags,
                                                         final ProgramVariable returnFlag,
                                                         final Services services) {
        List<ProgramVariable> result = new LinkedList<ProgramVariable>();
        result.addAll(createAndRegisterFlags(goal, breakFlags, services));
        result.addAll(createAndRegisterFlags(goal, continueFlags, services));
        if (returnFlag != null) {
            result.add(returnFlag);
            goal.addProgramVariable(returnFlag);
        }
        return result;
    }

    private List<ProgramVariable> createAndRegisterFlags(final Goal goal, final Collection<ProgramVariable> flags, final Services services) {
        List<ProgramVariable> result = new LinkedList<ProgramVariable>();
        for (ProgramVariable flag : flags) {
            String newName = TB.newName(services, flag.getProgramElementName().toString());
            ProgramVariable newFlag = new LocationVariable(new ProgramElementName(newName), flag.getKeYJavaType());
            result.add(newFlag);
            goal.addProgramVariable(newFlag);
        }
        return result;
    }

    private ProgramVariable createAndRegisterResultVariable(final Goal goal, final IProgramMethod method, final Services services) {
        final ProgramVariable result = method.isConstructor()
                ? TB.selfVar(services, method.getContainerType(), true)
                : TB.resultVar(services, method, true);
        if (result != null) {
            goal.addProgramVariable(result);
        }
        return result;
    }

    private ProgramVariable createAndRegisterExceptionVariable(final Goal goal, final IProgramMethod method, final Services services) {
        //TODO result should be of type Throwable and not of subtype Exception.
        final ProgramVariable result = TB.excVar(services, method, true);
        goal.addProgramVariable(result);
        return result;
    }

    private Map<LocationVariable, LocationVariable> createAndRegisterAtPreVars(Goal goal, List<LocationVariable> heaps, Services services) {
        Map<LocationVariable, LocationVariable> result = HeapContext.getBeforeAtPreVars(heaps, services, "BeforeBlock");
        for (LocationVariable v : result.values()) {
            goal.addProgramVariable(v);
        }
        return result;
    }

    private Term generatePrecondition(List<LocationVariable> heaps, BlockContract contract, Term self, ImmutableList<Term> variables, Map<LocationVariable, Term> atPres, Services services) {
        Term result = TB.tt();
        for (LocationVariable heap : heaps) {
            result = TB.and(result, contract.getPre(heap, TB.getBaseHeap(services), self, variables, atPres, services));
        }
        return result;
    }

    private Term generateWellFormedHeapsCondition(List<LocationVariable> heaps, Services services) {
        Term result = TB.tt();
        for (LocationVariable heap : heaps) {
            result = TB.and(result, TB.wellFormed(heap, services));
        }
        return result;
    }

    private Term generateReachableCondition(ImmutableSet<ProgramVariable> variables, Services services) {
        Term result = TB.tt();
        for (ProgramVariable variable : variables) {
            result = TB.and(result, TB.reachableValue(services, variable));
        }
        return result;
    }

    private Pair<Term, Map<LocationVariable, Map<Term, Term>>> generateRemembranceUpdateAndVariables(List<LocationVariable> heaps, ImmutableSet<ProgramVariable> variables, Services services) {
        Term remembranceUpdate = null;
        final Map<LocationVariable, Map<Term, Term>> remembranceVariables = new LinkedHashMap<LocationVariable, Map<Term, Term>>();
        for (LocationVariable heap : heaps) {
            // remember heap
            remembranceVariables.put(heap, new LinkedHashMap<Term, Term>());
            final LocationVariable variable = TB.heapAtPreVar(services, heap.name() + "BeforeBlock", heap.sort(), true);
            services.getNamespaces().programVariables().addSafely(variable);
            final Term update = TB.elementary(services, variable, TB.var(heap));
            if (remembranceUpdate == null) {
                remembranceUpdate = update;
            }
            else {
                remembranceUpdate = TB.parallel(remembranceUpdate, update);
            }
            remembranceVariables.get(heap).put(TB.var(heap), TB.var(variable));
        }
        for (ProgramVariable variable : variables) {
            // remember variable
            final String remembranceName = TB.newName(services, variable.name().toString() + "BeforeBlock");
            final LocationVariable remembranceVariable = new LocationVariable(new ProgramElementName(remembranceName), variable.getKeYJavaType());
            services.getNamespaces().programVariables().addSafely(remembranceVariable);
            remembranceUpdate = TB.parallel(remembranceUpdate, TB.elementary(services, remembranceVariable, TB.var(variable)));
            remembranceVariables.get(services.getTypeConverter().getHeapLDT().getHeap()).put(TB.var(variable), TB.var(remembranceVariable));
        }
        return new Pair<Term, Map<LocationVariable, Map<Term, Term>>>(remembranceUpdate, remembranceVariables);
    }

    private Map<LocationVariable, Term> generateModifiesConditions(List<LocationVariable> heaps, BlockContract contract, Term self, ImmutableList<Term> variables, Services services) {
        Map<LocationVariable, Term> result = new LinkedHashMap<LocationVariable, Term>();
        for (final LocationVariable heap : heaps) {
            result.put(heap, contract.getMod(heap, TB.var(heap), self, variables, services));
        }
        return result;
    }

    private Pair<Term, Term> generateAnonymisationUpdateAndWellFormedAnonymisationHeapsCondition(
            List<LocationVariable> heaps, ImmutableSet<ProgramVariable> variables, Map<LocationVariable, Term> modifies, Services services) {
        Term anonymisationUpdate = generateLocalVariablesAnonymisationUpdate(variables, services);
        Term wellFormedAnonymisationHeapsCondition = TB.tt();
        for (LocationVariable heap : heaps) {
            final Pair<Term, Term> anonymisationUpdateAndHeapTerm
                    = generateHeapAnonymisationUpdateAndAnonymisationHeapTerm(heap, modifies.get(heap), services);
            if (anonymisationUpdate == null) {
                anonymisationUpdate = anonymisationUpdateAndHeapTerm.first;
            }
            else {
                anonymisationUpdate = TB.parallel(anonymisationUpdate, anonymisationUpdateAndHeapTerm.first);
            }
            wellFormedAnonymisationHeapsCondition = TB.and(wellFormedAnonymisationHeapsCondition,
                    TB.wellFormed(anonymisationUpdateAndHeapTerm.second, services));
        }
        return new Pair<Term, Term>(anonymisationUpdate, wellFormedAnonymisationHeapsCondition);
    }

    private Term generateLocalVariablesAnonymisationUpdate(ImmutableSet<ProgramVariable> variables, Services services) {
        Term anonUpdate = null;
        for (ProgramVariable variable : variables) {
            final String anonymisationName = TB.newName(services, variable.name().toString());
            final Function anonymisationFunction = new Function(new Name(anonymisationName), variable.sort());
            services.getNamespaces().functions().addSafely(anonymisationFunction);
            final Term elementaryUpdate = TB.elementary(services, (LocationVariable) variable, TB.func(anonymisationFunction));
            if (anonUpdate == null) {
                anonUpdate = elementaryUpdate;
            }
            else {
                anonUpdate = TB.parallel(anonUpdate, elementaryUpdate);
            }
        }
        return anonUpdate;
    }

    private Pair<Term, Term> generateHeapAnonymisationUpdateAndAnonymisationHeapTerm(LocationVariable heap,
                                                                                     Term mod,
                                                                                     Services services) {
        final Name anonymisationName = new Name(TB.newName(services, "anon_" + heap.name() + "_block"));
        final Function anonymisationFunction = new Function(anonymisationName, services.getTypeConverter().getHeapLDT().targetSort());
        services.getNamespaces().functions().addSafely(anonymisationFunction);
        final Term anonymisationHeap = TB.func(anonymisationFunction);
        Term anonymisationUpdate = TB.skip();
        if (!TB.lessThanNothing().equals(mod)) {
            anonymisationUpdate = TB.anonUpd(heap, services, mod, anonymisationHeap);
        }
        return new Pair<Term, Term>(anonymisationUpdate, anonymisationHeap);
    }

    private Term generatePostcondition(List<LocationVariable> heaps, BlockContract contract, Term self, ImmutableList<Term> variables, Term result, Term exception, Map<LocationVariable, Term> atPres, Services services) {
        Term rezuld = TB.tt();
        for (LocationVariable heap : heaps) {
            rezuld = TB.and(rezuld, contract.getPost(heap, TB.getBaseHeap(services), self, variables, result, exception, atPres, services));
        }
        return rezuld;
    }

    private Term generateFrameCondition(List<LocationVariable> heaps, Map<LocationVariable, Term> modifiesConditions, Map<LocationVariable, Map<Term, Term>> remembranceVariables, Services services) {
        Term result = TB.tt();
        for (LocationVariable heap : heaps) {
            final Term modifiesCondition = modifiesConditions.get(heap);
            final Term frameCondition;
            if (TB.lessThanNothing().equals(modifiesCondition) && heap == services.getTypeConverter().getHeapLDT().getHeap()) {
                frameCondition = TB.frameStrictlyEmpty(services, TB.var(heap), remembranceVariables.get(heap));
            }
            else {
                frameCondition = TB.frame(services, TB.var(heap), remembranceVariables.get(heap), modifiesCondition);
            }
            result = TB.and(result, frameCondition);
        }
        return result;
    }

    private Term generateAtMostOneFlagSetCondition(Map<Label, ProgramVariable> breakFlags,
                                                   Map<Label, ProgramVariable> continueFlags,
                                                   ProgramVariable returnFlag, ProgramVariable exception,
                                                   Services services) {
        List<Term> notSetConditions = new LinkedList<Term>();
        for (ProgramVariable flag : breakFlags.values()) {
            notSetConditions.add(TB.equals(TB.var(flag), TB.FALSE(services)));
        }
        for (ProgramVariable flag : continueFlags.values()) {
            notSetConditions.add(TB.equals(TB.var(flag), TB.FALSE(services)));
        }
        if (returnFlag != null) {
            notSetConditions.add(TB.equals(TB.var(returnFlag), TB.FALSE(services)));
        }
        notSetConditions.add(TB.equals(TB.var(exception), TB.NULL(services)));

        Term result = TB.tt();
        for (Term notSetCondition : notSetConditions) {
            result = TB.and(result, notSetCondition);
        }
        for (Term onlySetNotSetCondition : notSetConditions) {
            Term condition = TB.not(onlySetNotSetCondition);
            for (Term notSetCondition : notSetConditions) {
                if (notSetCondition != onlySetNotSetCondition) {
                    condition = TB.and(condition, notSetCondition);
                }
            }
            result = TB.or(result, condition);
        }
        return result;
    }

    private ProgramVariable createLocalVariable(String varNameBase, String varType, Services services) {
        return createLocalVariable(varNameBase, services.getJavaInfo().getKeYJavaType(varType), services);
    }

    private ProgramVariable createLocalVariable(String varNameBase, KeYJavaType varType, Services services) {
        return KeYJavaASTFactory.localVariable(services.getVariableNamer().getTemporaryNameProposal(varNameBase), varType);
    }

    private void setUpValidityGoal(Goal goal, Term[] updates, Term[] assumptions,
                                   Instantiation instantiation, Map<Label, ProgramVariable> breakFlags,
                                   Map<Label, ProgramVariable> continueFlags, ProgramVariable returnFlag,
                                   ProgramVariable resultVariable, KeYJavaType returnType,
                                   ProgramVariable exceptionVariable, Term[] postconditions,
                                   PosInOccurrence occurrence, Services services) {
        goal.setBranchLabel("Validity");
        goal.addFormula(new SequentFormula(TB.applySequential(updates, TB.and(assumptions))), true, false);

        final List<Statement> statements = new LinkedList<Statement>();
        statements.addAll(declareFlagsFalseAndResultNull(breakFlags.values(), continueFlags.values(), returnFlag, resultVariable, returnType, services));
        statements.add(declareExceptionNull(exceptionVariable, services));
        // TODO What about label uniqueness?
        final Label breakOutLabel = new ProgramElementName("breakOut");
        final StatementBlock transformedBlock = replaceOuterBreaksContinuesAndReturns(
                instantiation.block, breakOutLabel, breakFlags, continueFlags, returnFlag, resultVariable, services);
        statements.add(constructTryCatchStatement(breakOutLabel, transformedBlock, exceptionVariable, services));

        // TODO Clean up.
        StatementBlock block = new StatementBlock(statements.toArray(new Statement[statements.size()]));

        Statement st = block;
        if (instantiation.context != null) {
            st = new MethodFrame(null, instantiation.context, block);
        }
        final boolean transaction = (instantiation.modality == Modality.DIA_TRANSACTION
                || instantiation.modality == Modality.BOX_TRANSACTION);
        goal.changeFormula(new SequentFormula(TB.applySequential(updates,
                TB.prog(instantiation.modality,
                        JavaBlock.createJavaBlock(transaction
                                ? new StatementBlock(new Statement[] {st, new TransactionStatement(de.uka.ilkd.key.java.recoderext.TransactionStatement.FINISH)})
                                : new StatementBlock(st)),
                        TB.and(postconditions)))), occurrence);
    }

    private List<Statement> declareFlagsFalseAndResultNull(final Collection<ProgramVariable> breakFlags,
                                                           final Collection<ProgramVariable> continueFlags,
                                                           final ProgramVariable returnFlag,
                                                           final ProgramVariable resultVariable,
                                                           final KeYJavaType returnType,
                                                           final Services services) {
        final List<Statement> result = new LinkedList<Statement>();
        for (ProgramVariable flag : breakFlags) {
            result.add(declareFlagFalse(flag, services));
        }
        for (ProgramVariable flag : continueFlags) {
            result.add(declareFlagFalse(flag, services));
        }
        if (returnFlag != null) {
            result.add(declareFlagFalse(returnFlag, services));
            if (returnType != null) {
                result.add(KeYJavaASTFactory.declare(resultVariable, NullLiteral.NULL, returnType));
            }
        }
        return result;
    }

    private Statement declareFlagFalse(final ProgramVariable flag, final Services services) {
        return KeYJavaASTFactory.declare(flag, BooleanLiteral.FALSE, services.getJavaInfo().getKeYJavaType("boolean"));
    }

    private Statement declareExceptionNull(final ProgramVariable exceptionVariable, final Services services) {
        return KeYJavaASTFactory.declare(exceptionVariable, NullLiteral.NULL, services.getJavaInfo().getKeYJavaType("java.lang.Throwable"));
    }

    private StatementBlock replaceOuterBreaksContinuesAndReturns(final StatementBlock block,
                                                                 final Label breakOutLabel,
                                                                 final Map<Label, ProgramVariable> breakFlags,
                                                                 final Map<Label, ProgramVariable> continueFlags,
                                                                 final ProgramVariable returnFlag,
                                                                 final ProgramVariable resultVariable,
                                                                 final Services services) {
        final OuterBreakContinueAndReturnReplacer transformer = new OuterBreakContinueAndReturnReplacer(
                block, breakOutLabel, breakFlags, continueFlags, returnFlag, resultVariable, services);
        transformer.start();
        return transformer.getResult();
    }

    private Statement constructTryCatchStatement(final Label breakOutLabel, final StatementBlock block,
                                                 final ProgramVariable exceptionVariable, final Services services) {
        ProgramVariable exceptionParameter = createLocalVariable("e", "java.lang.Throwable", services);
        Statement[] catchStatements = { KeYJavaASTFactory.assign(exceptionVariable, exceptionParameter) };
        Catch katch = KeYJavaASTFactory.catchClause(KeYJavaASTFactory.parameterDeclaration(
                services.getJavaInfo(),
                services.getJavaInfo().getKeYJavaType("java.lang.Throwable"),
                exceptionParameter), new StatementBlock(catchStatements));
        Branch[] branch = { katch };
        return new Try(new StatementBlock(new LabeledStatement(breakOutLabel, block)), branch);
    }

    private void setUpPreconditionGoal(final Goal goal, final Term update, final Term[] preconditions, final PosInOccurrence occurrence) {
        goal.setBranchLabel("Precondition");
        goal.changeFormula(new SequentFormula(TB.apply(update, TB.and(preconditions))), occurrence);
    }

    private void setUpUsageGoal(Goal goal, StatementBlock block, Term[] updates, Term[] assumptions, Map<Label, ProgramVariable> breakFlags,
                                Map<Label, ProgramVariable> continueFlags, ProgramVariable returnFlag, ProgramVariable result,
                                ProgramVariable exception, Term formula, PosInOccurrence occurrence, Services services) {
        goal.setBranchLabel("Usage");
        goal.addFormula(new SequentFormula(TB.applySequential(updates, TB.and(assumptions))), true, false);

        // TODO Clean up.
        Term newFormula = TB.prog((Modality) formula.op(),
                replaceBlock(formula.javaBlock(), block,
                        constructIfCascade(breakFlags, continueFlags, returnFlag, result, exception),
                        services),
                formula.sub(0));
        goal.changeFormula(new SequentFormula(TB.applySequential(updates, newFormula)), occurrence);
    }

    private JavaBlock replaceBlock(final JavaBlock java, final StatementBlock oldBlock, final StatementBlock newBlock, final Services services) {
        assert java.program() != null;
        // TODO Extract.
        Statement newProgram = (Statement) (new CreatingASTVisitor(java.program(), false, services) {
            private boolean done = false;

            public ProgramElement go() {
                stack.push(new ExtList());
                walk(root());
                ExtList el = stack.peek();
                return el.get(ProgramElement.class);
            }

            public void doAction(ProgramElement node) {
                if (!done && node == oldBlock) {
                    done = true;
                    addChild(newBlock);
                    changed();
                }
                else {
                    super.doAction(node);
                }
            }
        }).go();
        return JavaBlock.createJavaBlock(newProgram instanceof StatementBlock ? (StatementBlock) newProgram : new StatementBlock(newProgram));
    }

    private StatementBlock constructIfCascade(final Map<Label, ProgramVariable> breakFlags,
                                              final Map<Label, ProgramVariable> continueFlags,
                                              final ProgramVariable returnFlag,
                                              final ProgramVariable resultVariable,
                                              final ProgramVariable exceptionVariable) {
        List<If> ifCascade = new ArrayList<If>();
        for (Map.Entry<Label, ProgramVariable> flag : breakFlags.entrySet()) {
            ifCascade.add(KeYJavaASTFactory.ifThen(flag.getValue(), KeYJavaASTFactory.breakStatement(flag.getKey())));
        }
        for (Map.Entry<Label, ProgramVariable> flag : continueFlags.entrySet()) {
            ifCascade.add(KeYJavaASTFactory.ifThen(flag.getValue(), KeYJavaASTFactory.continueStatement(flag.getKey())));
        }
        if (returnFlag != null) {
            ifCascade.add(KeYJavaASTFactory.ifThen(returnFlag, KeYJavaASTFactory.returnClause(resultVariable)));
        }
        ifCascade.add(KeYJavaASTFactory.ifThen(
                new NotEquals(new ExtList(new Expression[] {exceptionVariable, NullLiteral.NULL})),
                KeYJavaASTFactory.throwClause(exceptionVariable)));
        return new StatementBlock(ifCascade.toArray(new Statement[ifCascade.size()]));
    }

    @Override
    public BlockContractBuiltInRuleApp createApp(final PosInOccurrence occurrence) {
        return new BlockContractBuiltInRuleApp(this, occurrence);
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

    public static final class Instantiation {
        public final Term update;
        public final Term formula;
        public final Modality modality;
        public final Term self;
        public final StatementBlock block;
        public final ExecutionContext context;

        public Instantiation(Term update, Term formula, Modality modality, Term self, StatementBlock block, ExecutionContext context) {
            assert update != null;
            assert update.sort() == Sort.UPDATE;
            assert formula != null;
            assert formula.sort() == Sort.FORMULA;
            assert modality != null;
            assert block != null;
            this.update = update;
            this.formula = formula;
            this.modality = modality;
            this.self = self;
            this.block = block;
            this.context = context;
        }
    }

}