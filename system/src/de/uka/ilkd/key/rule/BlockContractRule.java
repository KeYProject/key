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

    private Term lastFocusTerm;
    private Instantiation lastInstantiation;

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    private BlockContractRule() {
    }

    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------

    public static ImmutableSet<BlockContract> getApplicableContracts(Instantiation instantiation, Services services) {
        if (instantiation == null) {
            return DefaultImmutableSet.<BlockContract>nil();
        }
        return getApplicableContracts(services, instantiation.block, instantiation.modality);
    }

    static ImmutableSet<BlockContract> getApplicableContracts(Services services, StatementBlock block, Modality modality) {
        ImmutableSet<BlockContract> result = services.getSpecificationRepository().getBlockContracts(block, modality);
        if (modality == Modality.BOX) {
            result = result.union(services.getSpecificationRepository().getBlockContracts(block, Modality.DIA));
        }
        else if (modality == Modality.BOX_TRANSACTION) {
            result = result.union(services.getSpecificationRepository().getBlockContracts(block, Modality.DIA_TRANSACTION));
        }
        return result;
    }

    private Instantiation instantiate(Term focusTerm, Services services) {
        if (focusTerm == lastFocusTerm) {
            return lastInstantiation;
        }
        else {
            final Instantiation result = computeInstantiation(focusTerm, services);
            lastFocusTerm = focusTerm;
            lastInstantiation = result;
            return result;
        }
    }

    private static Pair<Term, Term> extractUpdate(Term focusTerm) {
        if (focusTerm.op() instanceof UpdateApplication) {
            return new Pair<Term, Term>(UpdateApplication.getUpdate(focusTerm), UpdateApplication.getTarget(focusTerm));
        } else {
            return new Pair<Term, Term>(TB.skip(), focusTerm);
        }
    }

    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    public static Instantiation computeInstantiation(final Term formula, final Services services) {
        final Pair<Term, Term> updateAndTarget = extractUpdate(formula);
        final Term update = updateAndTarget.first;
        final Term target = updateAndTarget.second;

        if (!(target.op() instanceof Modality)) {
            return null;
        }
        final Modality modality = (Modality) target.op();

        //final StatementBlock block = JavaTools.getActiveBlock(target.javaBlock());
        //final StatementBlock block = JavaTools.getActiveBlock(target.javaBlock());
        // get first block that has an applicable contract
        StatementBlock block = null;
        SourceElement element = target.javaBlock().program().getFirstElement();
        while ((element instanceof ProgramPrefix || element instanceof CatchAllStatement)
                && !(element instanceof StatementBlock && ((StatementBlock) element).isEmpty())) {
            if (element instanceof StatementBlock
                    && !getApplicableContracts(services, (StatementBlock) element, modality).isEmpty()) {
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
            block = (StatementBlock) element;
        }
        if (block == null) {
            return null;
        }

        final MethodFrame frame = JavaTools.getInnermostMethodFrame(target.javaBlock(), services);
        final Term self = (frame == null ? null : MiscTools.getSelfTerm(frame, services));
        final ExecutionContext context = (frame == null ? null : (ExecutionContext) frame.getExecutionContext());

        return new Instantiation(update, target, modality, self, block, context);
    }

    @Override
    public boolean isApplicable(final Goal goal, final PosInOccurrence occurrence) {
        if (occurrence == null || !occurrence.isTopLevel() || occurrence.isInAntec()) {
            return false;
        }
        final Instantiation instantiation = instantiate(occurrence.subTerm(), goal.proof().getServices());
        if (instantiation == null) {
            return false;
        }
        final ImmutableSet<BlockContract> contracts = getApplicableContracts(goal.proof().getServices(), instantiation.block, instantiation.modality);
        return !contracts.isEmpty();
    }

    @Override
    public ImmutableList<Goal> apply(final Goal goal, final Services services, final RuleApp application) throws RuleAbortException {
        return apply(goal, services, (BlockContractBuiltInRuleApp) application);
    }

    public ImmutableList<Goal> apply(final Goal goal, final Services services, final BlockContractBuiltInRuleApp application) throws RuleAbortException {
        final Instantiation instantiation = instantiate(application.posInOccurrence().subTerm(), services);
        final BlockContract contract = application.getContract();
        //assert contract.getBlock().equals(instantiation.block);
        final IProgramMethod method = contract.getTarget();
        final Term contextUpdate = instantiation.update;

        // TODO Refactor.
        List<ProgramVariable> localInVariables = new LinkedList<ProgramVariable>();
        for (ProgramVariable variable : MiscTools.getLocalIns(instantiation.block, services)) {
            localInVariables.add(variable);
        }
        Collections.reverse(localInVariables);
        final Map<Label, ProgramVariable> breakFlags = contract.getInternalBreakFlags();
        for (ProgramVariable flag : breakFlags.values()) {
            String newName = TB.newName(services, flag.getProgramElementName().toString());
            ProgramVariable newFlag = new LocationVariable(new ProgramElementName(newName), flag.getKeYJavaType());
            localInVariables.add(newFlag);
            goal.addProgramVariable(newFlag);
        }
        final Map<Label, ProgramVariable> continueFlags = contract.getInternalContinueFlags();
        for (ProgramVariable flag : continueFlags.values()) {
            String newName = TB.newName(services, flag.getProgramElementName().toString());
            ProgramVariable newFlag = new LocationVariable(new ProgramElementName(newName), flag.getKeYJavaType());
            localInVariables.add(newFlag);
            goal.addProgramVariable(newFlag);
        }
        final ProgramVariable returnFlag = contract.getInternalReturnFlag();
        if (returnFlag != null) {
            localInVariables.add(returnFlag);
            goal.addProgramVariable(returnFlag);
        }
        final ProgramVariable resultVar = method.isConstructor()
                ? TB.selfVar(services, contract.getKJT(), true)
                : TB.resultVar(services, method, true);
        if (resultVar != null) {
            goal.addProgramVariable(resultVar);
        }
        //TODO excVar should be of type Throwable and not of subtype Exception.
        final ProgramVariable excVar = TB.excVar(services, method, true);
        goal.addProgramVariable(excVar);

        //Modality modality = (Modality) TermBuilder.DF.goBelowUpdates(application.posInOccurrence().subTerm()).op();
        final List<LocationVariable> heaps = HeapContext.getModHeaps(goal.proof().getServices(), instantiation.modality.transaction());
        Map<LocationVariable, LocationVariable> atPreVars = HeapContext.getBeforeAtPreVars(heaps, services, "BeforeBlock_" + contract.getTarget().getName());
        for (LocationVariable v : atPreVars.values()) {
            goal.addProgramVariable(v);
        }
        final Map<LocationVariable, Term> atPres = HeapContext.getAtPres(atPreVars, services);




        final Term precondition = generatePrecondition(heaps, contract, instantiation.self, TB.var(localInVariables), atPres, services);
        final Term wellFormedHeapsCondition = generateWellFormedHeapsCondition(heaps, services);
        final Term reachableInCondition = generateReachableCondition(localInVariables, services);
        final Term[] preconditions = new Term[] {precondition, wellFormedHeapsCondition, reachableInCondition};

        final ImmutableSet<ProgramVariable> localOutVariables = MiscTools.getLocalOuts(instantiation.block, services);
        final Pair<Term, Map<LocationVariable, Map<Term, Term>>> remembranceUpdateAndVariables
                = generateRemembranceUpdateAndVariables(heaps, localOutVariables, services);
        final Term remembranceUpdate = remembranceUpdateAndVariables.first;
        final Map<LocationVariable, Map<Term, Term>> remembranceVariables = remembranceUpdateAndVariables.second;
        final Map<LocationVariable, Term> modifiesConditions = generateModifiesConditions(heaps, contract, instantiation.self, TB.var(localInVariables), services);
        final Pair<Term, Term> anonymisationUpdateAndWellFormedAnonymisationHeapsCondition
                = generateAnonymisationUpdateAndWellFormedAnonymisationHeapsCondition(heaps, localOutVariables, modifiesConditions, services);
        final Term anonymisationUpdate = anonymisationUpdateAndWellFormedAnonymisationHeapsCondition.first;
        final Term postcondition = generatePostcondition(heaps, contract, instantiation.self, TB.var(localInVariables), TB.var(resultVar), TB.var(excVar), atPres, services);
        final Term frameCondition = generateFrameCondition(heaps, modifiesConditions, remembranceVariables, services);
        final Term atMostOneFlagSetCondition = generateAtMostOneFlagSetCondition(breakFlags, continueFlags, returnFlag, excVar, services);
        final Term wellFormedAnonymisationHeapsCondition = anonymisationUpdateAndWellFormedAnonymisationHeapsCondition.second;
        final Term reachableOutCondition = generateReachableCondition(localOutVariables, services);

        final ImmutableList<Goal> result = goal.split(3);
        setUpValidityGoal(result.tail().tail().head(),
                new Term[] {contextUpdate, remembranceUpdate},
                preconditions, instantiation,
                breakFlags, continueFlags, returnFlag, resultVar, contract.getTarget().getReturnType(), excVar,
                new Term[] {postcondition, frameCondition/*, atMostOneFlagSetCondition*/},
                application.posInOccurrence(), services);
        setUpPreconditionGoal(result.tail().head(), contextUpdate, preconditions, application.posInOccurrence());
        setUpUsageGoal(result.head(), instantiation.block,
                new Term[] {contextUpdate, remembranceUpdate, anonymisationUpdate},
                new Term[] {postcondition, wellFormedAnonymisationHeapsCondition, reachableOutCondition, atMostOneFlagSetCondition},
                breakFlags, continueFlags, returnFlag, resultVar, excVar,
                instantiation.formula, application.posInOccurrence(), services);

        return result;
    }

    private Term generatePrecondition(List<LocationVariable> heaps, BlockContract contract, Term self, ImmutableList<Term> variables, Map<LocationVariable, Term> atPres, Services services) {
        Term result = TB.tt();
        for (LocationVariable heap : heaps) {
            //TODO variables are only localInVariables plus flags. But paramVars of getPre are ALL local variables plus flags. (see JMLSpecFactory)
            //     This is problematic because the variable replacement map is constructed by position in the list.
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

    private Term generateReachableCondition(Iterable<ProgramVariable> variables, Services services) {
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
                                   ProgramVariable result, KeYJavaType returnType,
                                   ProgramVariable exception, Term[] postconditions,
                                   PosInOccurrence occurrence, Services services) {
        goal.setBranchLabel("Validity");
        goal.addFormula(new SequentFormula(TB.applySequential(updates, TB.and(assumptions))), true, false);

        /*final OuterBreakContinueAndReturnReplacer wir = (OuterBreakContinueAndReturnReplacer) AbstractTermTransformer.BLOCK_TRANSFORMER;
        SVInstantiations svInst = SVInstantiations.EMPTY_SVINSTANTIATIONS.replace(
                null, null, instantiation.innermostExecutionContext, null, services);
        for (SchemaVariable sv : wir.neededInstantiations(instantiation.block, svInst)) {
            assert sv instanceof ProgramSV;
            svInst = svInst.addInteresting(sv, (Name) new ProgramElementName(sv.name().toString()), services);
        }
        Term bodyTerm = TB.tf().createTerm(wir, formula, TB.and(postconditions));
        bodyTerm = wir.transform(bodyTerm, svInst, services);*/

        final List<Statement> statements = new ArrayList<Statement>();
        for (ProgramVariable flag : breakFlags.values()) {
            statements.add(declareFlag(flag, services));
        }
        for (ProgramVariable flag : continueFlags.values()) {
            statements.add(declareFlag(flag, services));
        }
        if (returnFlag != null) {
            statements.add(declareFlag(returnFlag, services));
            if (returnType != null) {
                statements.add(KeYJavaASTFactory.declare(result, NullLiteral.NULL, returnType));
            }
        }
        statements.add(KeYJavaASTFactory.declare(exception, NullLiteral.NULL, services.getJavaInfo().getKeYJavaType("java.lang.Throwable")));

        Label breakOutLabel = new ProgramElementName("breakOut");

        OuterBreakContinueAndReturnReplacer transformer = new OuterBreakContinueAndReturnReplacer(instantiation.block, breakOutLabel, breakFlags, continueFlags, returnFlag, result, services);
        transformer.start();

        ProgramVariable exceptionParameter = createLocalVariable("e", "java.lang.Throwable", services);
        Statement[] catchStatements = { KeYJavaASTFactory.assign(exception, exceptionParameter) };
        Catch katch = KeYJavaASTFactory.catchClause(KeYJavaASTFactory.parameterDeclaration(
                services.getJavaInfo(),
                services.getJavaInfo().getKeYJavaType("java.lang.Throwable"),
                exceptionParameter), new StatementBlock(catchStatements));
        Branch[] branch = { katch };
        Statement dry = new Try(new StatementBlock(new LabeledStatement(breakOutLabel, transformer.getResult())), branch);

        statements.add(dry);

        StatementBlock block = new StatementBlock(statements.toArray(new Statement[statements.size()]));

        Statement st = block;
        if (instantiation.innermostExecutionContext != null) {
            st = new MethodFrame(null, instantiation.innermostExecutionContext, block);
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

    private Statement declareFlag(final ProgramVariable flag, Services services) {
        return KeYJavaASTFactory.declare(flag, BooleanLiteral.FALSE, services.getJavaInfo().getKeYJavaType("boolean"));
    }

    private void setUpPreconditionGoal(Goal goal, Term update, Term[] preconditions, PosInOccurrence occurrence) {
        goal.setBranchLabel("Precondition");
        goal.changeFormula(new SequentFormula(TB.apply(update, TB.and(preconditions))), occurrence);
    }

    private void setUpUsageGoal(Goal goal, StatementBlock block, Term[] updates, Term[] assumptions, Map<Label, ProgramVariable> breakFlags,
                                Map<Label, ProgramVariable> continueFlags, ProgramVariable returnFlag, ProgramVariable result,
                                ProgramVariable exception, Term formula, PosInOccurrence occurrence, Services services) {
        goal.setBranchLabel("Usage");
        goal.addFormula(new SequentFormula(TB.applySequential(updates, TB.and(assumptions))), true, false);

        Term restPsi = TB.prog((Modality) formula.op(),
                replaceBlock(formula.javaBlock(), block,
                        constructIfCascade(breakFlags, continueFlags, returnFlag, result, exception),
                        services),
                formula.sub(0));
        goal.changeFormula(new SequentFormula(TB.applySequential(updates, restPsi)), occurrence);
    }

    private JavaBlock replaceBlock(JavaBlock jb, final StatementBlock oldBlock, final StatementBlock newBlock, Services services) {
        assert jb.program() != null;
        Statement newProg = (Statement)
                (new CreatingASTVisitor(jb.program(), false, services) {
                    private boolean done = false;

                    public ProgramElement go() {
                        stack.push(new ExtList());
                        walk(root());
                        ExtList el = stack.peek();
                        return el.get(ProgramElement.class);
                    }

                    public void doAction(ProgramElement node) {
                        if(!done && node == oldBlock) {
                            done = true;
                            addChild(newBlock);
                            changed();
                        } else {
                            super.doAction(node);
                        }
                    }
                }).go();

        StatementBlock newSB = newProg instanceof StatementBlock
                ? (StatementBlock)newProg
                : new StatementBlock(newProg);
        return JavaBlock.createJavaBlock(newSB);
    }

    private StatementBlock constructIfCascade(Map<Label, ProgramVariable> breakFlags,
                                              Map<Label, ProgramVariable> continueFlags,
                                              ProgramVariable returnFlag,
                                              ProgramVariable result,
                                              ProgramVariable exception) {
        List<If> ifCascade = new ArrayList<If>();
        for (Map.Entry<Label, ProgramVariable> flag : breakFlags.entrySet()) {
            ifCascade.add(KeYJavaASTFactory.ifThen(flag.getValue(), KeYJavaASTFactory.breakStatement(flag.getKey())));
        }
        for (Map.Entry<Label, ProgramVariable> flag : continueFlags.entrySet()) {
            ifCascade.add(KeYJavaASTFactory.ifThen(flag.getValue(), KeYJavaASTFactory.breakStatement(flag.getKey())));
        }
        if (returnFlag != null) {
            ifCascade.add(KeYJavaASTFactory.ifThen(returnFlag, KeYJavaASTFactory.returnClause(result)));
        }
        ifCascade.add(KeYJavaASTFactory.ifThen(
                new NotEquals(new ExtList(new Expression[] {exception, NullLiteral.NULL})),
                KeYJavaASTFactory.throwClause(exception)));
        return new StatementBlock(ifCascade.toArray(new Statement[ifCascade.size()]));
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
    public BlockContractBuiltInRuleApp createApp(PosInOccurrence occurrence) {
        return new BlockContractBuiltInRuleApp(this, occurrence);
    }

    //-------------------------------------------------------------------------
    // inner classes
    //-------------------------------------------------------------------------

    public static final class Instantiation {
        public final Term update;
        public final Term formula;
        public final Modality modality;
        public final Term self;
        public final StatementBlock block;
        public final ExecutionContext innermostExecutionContext;

        public Instantiation(Term update, Term formula, Modality modality, Term self, StatementBlock block, ExecutionContext innermostExecutionContext) {
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
            this.innermostExecutionContext = innermostExecutionContext;
        }
    }

}