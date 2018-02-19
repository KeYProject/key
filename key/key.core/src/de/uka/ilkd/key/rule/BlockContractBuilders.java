package de.uka.ilkd.key.rule;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.informationflow.proof.InfFlowCheckInfo;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.expression.operator.NotEquals;
import de.uka.ilkd.key.java.statement.Branch;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.TransactionStatement;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.java.visitor.OuterBreakContinueAndReturnReplacer;
import de.uka.ilkd.key.java.visitor.ProgramElementReplacer;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.macros.WellDefinednessMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.StrategyInfoUndoMethod;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.rule.AbstractBlockContractRule.BlockContractHint;
import de.uka.ilkd.key.rule.AbstractBlockContractRule.Instantiation;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.BlockContract.Terms;
import de.uka.ilkd.key.speclang.BlockWellDefinedness;

/**
 * This contains various builders used in building formulae and terms for block contracts.
 */
public class BlockContractBuilders {
    
    /*
     * TODO
     * This should be renamed to anonOut or something similar.
     * Also, all references to "anonymisation" should be changed to refer to
     * "output anonymisation" instead.
     */
    public static final String ANONYMISATION_PREFIX = "anon_";

    private BlockContractBuilders() { }
    
    /**
     * This class is used to construct {@code block'} from {@code block} (see Wacker 2012, 3.3).
     */
    public static final class ValidityProgramConstructor {

        private final Iterable<Label> labels;
        private final StatementBlock block;
        private final BlockContract.Variables variables;
        private final Services services;
        private final List<Statement> statements;
        private final ProgramVariable exceptionParameter;

        public ValidityProgramConstructor(final Iterable<Label> labels,
                                          final StatementBlock block,
                                          final BlockContract.Variables variables,
                                          final ProgramVariable exceptionParameter,
                                          final Services services) {
            this.labels = labels;
            this.block = block;
            this.variables = variables;
            this.services = services;
            this.exceptionParameter = exceptionParameter;
            statements = new LinkedList<Statement>();
        }

        public StatementBlock construct()
        {
            declareFlagsFalse();
            declareResultDefault();
            declareExceptionNull();
            executeBlockSafely();
            return new StatementBlock(statements.toArray(new Statement[statements.size()]));
        }

        private void declareFlagsFalse()
        {
            declareFlagsFalse(variables.breakFlags.values());
            declareFlagsFalse(variables.continueFlags.values());
            if (variables.returnFlag != null) {
                declareFlagFalse(variables.returnFlag);
            }
        }

        private void declareFlagsFalse(final Collection<ProgramVariable> flags)
        {
            for (ProgramVariable flag : flags) {
                declareFlagFalse(flag);
            }
        }

        private void declareFlagFalse(final ProgramVariable flag) {
            statements.add(KeYJavaASTFactory.declare(flag, BooleanLiteral.FALSE,
                             services.getJavaInfo().getKeYJavaType("boolean")));
        }

        private void declareResultDefault() {
            if (occursReturnAndIsReturnTypeNotVoid()) {
                KeYJavaType resultType = variables.result.getKeYJavaType();
                statements.add(KeYJavaASTFactory.declare(
                        variables.result, resultType.getDefaultValue(), resultType));
            }
        }

        private boolean occursReturnAndIsReturnTypeNotVoid() {
            return variables.returnFlag != null && variables.result != null;
        }

        private void declareExceptionNull() {
            statements.add(KeYJavaASTFactory.declare(
                    variables.exception, NullLiteral.NULL, variables.exception.getKeYJavaType()));
        }

        private void executeBlockSafely() {
            final Label breakOutLabel = new ProgramElementName("breakOut");
            final StatementBlock almostSafeBlock =
                    replaceOuterBreaksContinuesAndReturns(block, breakOutLabel);
            final Statement labeledAlmostSafeBlock = label(almostSafeBlock, labels);
            final Statement safeStatement = wrapInTryCatch(labeledAlmostSafeBlock,
                                                           exceptionParameter);
            statements.add(new LabeledStatement(breakOutLabel, safeStatement, PositionInfo.UNDEFINED));
        }

        private Statement label(final StatementBlock block, Iterable<Label> labels)
        {
            Statement result = block;
            for (Label label : labels) {
                result = new LabeledStatement(label, result, PositionInfo.UNDEFINED);
            }
            return result;
        }

        private StatementBlock replaceOuterBreaksContinuesAndReturns(final StatementBlock block,
                                                                     final Label breakOutLabel) {
            return new OuterBreakContinueAndReturnReplacer(
                block, labels, breakOutLabel, variables.breakFlags, variables.continueFlags,
                variables.returnFlag, variables.result, services
            ).replace();
        }

        private Statement wrapInTryCatch(final Statement labeldBlock,
                                         final ProgramVariable exceptionParameter) {
            Catch katch =
                    KeYJavaASTFactory.catchClause(KeYJavaASTFactory.parameterDeclaration(
                                                                    services.getJavaInfo(),
                                                                    exceptionParameter.getKeYJavaType(),
                                                                    exceptionParameter),
                                                  new StatementBlock(KeYJavaASTFactory.assign(
                                                          variables.exception, exceptionParameter)));
            return new Try(new StatementBlock(labeldBlock), new Branch[] {katch});
        }
    }
    
    /**
     * This class contains methods to create new variables from the contract's placeholder variables
     * (see {@link BlockContract#getPlaceholderVariables()}), and adds them to the goal.
     */
    public static final class VariablesCreatorAndRegistrar {

        private final Goal goal;
        private final BlockContract.Variables placeholderVariables;
        private final TermServices services;

        public VariablesCreatorAndRegistrar(final Goal goal,
                                            final BlockContract.Variables placeholderVariables,
                                            final TermServices services) {
            this.goal = goal;
            this.placeholderVariables = placeholderVariables;
            this.services = services;
        }

        public BlockContract.Variables createAndRegister(Term self)
        {
            return new BlockContract.Variables(
                self != null ? self.op(ProgramVariable.class) : null,
                createAndRegisterFlags(placeholderVariables.breakFlags),
                createAndRegisterFlags(placeholderVariables.continueFlags),
                createAndRegisterVariable(placeholderVariables.returnFlag),
                createAndRegisterVariable(placeholderVariables.result),
                createAndRegisterVariable(placeholderVariables.exception),
                createAndRegisterRemembranceVariables(placeholderVariables.remembranceHeaps),
                createAndRegisterRemembranceVariables(placeholderVariables.remembranceLocalVariables),
                services
            );
        }

        private Map<Label, ProgramVariable> createAndRegisterFlags(final Map<Label,
                                                                   ProgramVariable> placeholderFlags) {
            Map<Label, ProgramVariable> result = new LinkedHashMap<Label, ProgramVariable>();
            for (Map.Entry<Label, ProgramVariable> flag : placeholderFlags.entrySet()) {
                result.put(flag.getKey(), createAndRegisterVariable(flag.getValue()));
            }
            return result;
        }

        private Map<LocationVariable, LocationVariable> createAndRegisterRemembranceVariables(
                final Map<LocationVariable, LocationVariable> remembranceVariables) {
            final Map<LocationVariable, LocationVariable> result =
                    new LinkedHashMap<LocationVariable, LocationVariable>();
            for (Map.Entry<LocationVariable, LocationVariable> remembranceVariable
                    : remembranceVariables.entrySet()) {
                result.put(remembranceVariable.getKey(),
                           createAndRegisterVariable(remembranceVariable.getValue()));
            }
            return result;
        }

        private LocationVariable createAndRegisterVariable(final ProgramVariable placeholderVariable)
        {
            if (placeholderVariable != null) {
                String newName = services.getTermBuilder().newName(placeholderVariable.name().toString());
                LocationVariable newVariable =
                        new LocationVariable(new ProgramElementName(newName),
                                             placeholderVariable.getKeYJavaType());
                
                if (goal != null) {
                    goal.addProgramVariable(newVariable);
                } else {
                    Namespace<IProgramVariable> progVarNames = services.getNamespaces().programVariables();
                    if (newVariable != null && progVarNames.lookup(placeholderVariable.name()) == null) {
                        progVarNames.addSafely(newVariable);
                    }
                }
                
                return newVariable;
            }
            else {
                return null;
            }
        }
    }

    public static final class UpdatesBuilder extends TermBuilder {

        private final BlockContract.Variables variables;

        public UpdatesBuilder(final BlockContract.Variables variables, final Services services) {
            super(services.getTermFactory(), services);
            this.variables = variables;
        }

        public Term buildRemembranceUpdate(final List<LocationVariable> heaps) {
            Term result = skip();
            for (LocationVariable heap : heaps) {
                final Term update = elementary(variables.remembranceHeaps.get(heap), var(heap));
                result = parallel(result, update);
            }
            for (Map.Entry<LocationVariable, LocationVariable> remembranceVariable
                    : variables.remembranceLocalVariables.entrySet()) {
                result = parallel(result, elementary(remembranceVariable.getValue(),
                                                     var(remembranceVariable.getKey())));
            }
            return result;
        }

        public Term buildAnonymisationUpdate(final Map<LocationVariable, Function> anonymisationHeaps,
                                             final Map<LocationVariable, Term> modifiesClauses) {
            Term result = buildLocalVariablesAnonymisationUpdate();
            for (Map.Entry<LocationVariable, Function> anonymisationHeap
                    : anonymisationHeaps.entrySet()) {
                Term anonymisationUpdate = skip();
                final Term modifiesClause = modifiesClauses.get(anonymisationHeap.getKey());
                if (!modifiesClause.equals(strictlyNothing())) {
                    anonymisationUpdate = anonUpd(anonymisationHeap.getKey(), modifiesClause,
                          services.getTermBuilder().label(services.getTermBuilder().func(anonymisationHeap.getValue()),
                                                           ParameterlessTermLabel.ANON_HEAP_LABEL));
                }
                result = parallel(result, anonymisationUpdate);
            }
            return result;
        }

        private Term buildLocalVariablesAnonymisationUpdate() {
            Term result = skip();
            final Collection<LocationVariable> localOutVariables =
                    variables.remembranceLocalVariables.keySet();
            for (LocationVariable variable : localOutVariables) {
                final String anonymisationName = newName(ANONYMISATION_PREFIX + variable.name());
                final Function anonymisationFunction =
                        new Function(new Name(anonymisationName), variable.sort(), true);
                services.getNamespaces().functions().addSafely(anonymisationFunction);
                final Term elementaryUpdate = elementary(variable, func(anonymisationFunction));
                result = parallel(result, elementaryUpdate);
            }
            return result;
        }

    }
    
    public static final class ConditionsAndClausesBuilder extends TermBuilder {

        private final BlockContract contract;
        private final List<LocationVariable> heaps;
        private final BlockContract.Variables variables;
        
        protected final BlockContract.Terms terms;

        public ConditionsAndClausesBuilder(final BlockContract contract,
                                           final List<LocationVariable> heaps,
                                           final BlockContract.Variables variables,
                                           final Term self, final Services services) {
            super(services.getTermFactory(), services);
            this.contract = contract;
            this.heaps = heaps;
            this.variables = variables;
            this.terms = variables.termify(self);
        }

        public Term buildPrecondition()
        {
            Term result = tt();
            for (LocationVariable heap : heaps) {
                result = and(result,
                             contract.getPrecondition(heap, getBaseHeap(), terms.self,
                                                      terms.remembranceHeaps, services));
            }
            return result;
        }

        public Term buildWellFormedHeapsCondition()
        {
            Term result = tt();
            for (LocationVariable heap : heaps) {
                result = and(result, wellFormed(heap));
            }
            return result;
        }

        public Term buildReachableInCondition(final ImmutableSet<ProgramVariable> localInVariables)
        {
            return buildReachableCondition(localInVariables);
        }

        public Term buildReachableOutCondition(final ImmutableSet<ProgramVariable> localOutVariables)
        {
            final Term reachableResult =
                    (variables.result != null) ?
                    reachableValue(variables.result) : services.getTermBuilder().tt();
            return and(
                buildReachableCondition(localOutVariables),
                reachableResult,
                reachableValue(variables.exception)
            );
        }

        public Term buildReachableCondition(final ImmutableSet<ProgramVariable> variables)
        {
            Term result = tt();
            for (ProgramVariable variable : variables) {
                result = and(result, reachableValue(variable));
            }
            return result;
        }

        public Map<LocationVariable, Term> buildModifiesClauses()
        {
            Map<LocationVariable, Term> result = new LinkedHashMap<LocationVariable, Term>();
            for (final LocationVariable heap : heaps) {
                result.put(heap, contract.getModifiesClause(heap, var(heap), terms.self, services));
            }
            return result;
        }

        public Term buildPostcondition()
        {
            Term result = tt();
            for (LocationVariable heap : heaps) {
                result = and(result, contract.getPostcondition(heap, getBaseHeap(),
                                                               terms, services));
            }
            return result;
        }

        public Term buildFrameCondition(final Map<LocationVariable, Term> modifiesClauses)
        {
            Term result = tt();
            Map<LocationVariable, Map<Term, Term>> remembranceVariables =
                    constructRemembranceVariables();
            for (LocationVariable heap : heaps) {
                final Term modifiesClause = modifiesClauses.get(heap);
                final Term frameCondition;
                if (modifiesClause.equals(strictlyNothing())) {
                    frameCondition = frameStrictlyEmpty(var(heap), remembranceVariables.get(heap));
                }
                else {
                    frameCondition = frame(var(heap), remembranceVariables.get(heap), modifiesClause);
                }
                result = and(result, frameCondition);
            }
            return result;
        }

        private Map<LocationVariable, Map<Term, Term>> constructRemembranceVariables()
        {
            Map<LocationVariable, Map<Term, Term>> result =
                    new LinkedHashMap<LocationVariable, Map<Term, Term>>();
            for (Map.Entry<LocationVariable, LocationVariable> remembranceHeap
                    : variables.remembranceHeaps.entrySet()) {
                final LocationVariable heap = remembranceHeap.getKey();
                result.put(heap, new LinkedHashMap<Term, Term>());
                result.get(heap).put(var(heap), var(remembranceHeap.getValue()));
            }
            for (Map.Entry<LocationVariable, LocationVariable> remembranceLocalVariable
                    : variables.remembranceLocalVariables.entrySet()) {
                result.get(getBaseHeapFunction()).put(var(remembranceLocalVariable.getKey()),
                                                      var(remembranceLocalVariable.getValue()));
            }
            return result;
        }

        private LocationVariable getBaseHeapFunction()
        {
            return services.getTypeConverter().getHeapLDT().getHeap();
        }

        public Term buildWellFormedAnonymisationHeapsCondition(
                final Map<LocationVariable, Function> anonymisationHeaps) {
            Term result = tt();
            for (Function anonymisationFunction : anonymisationHeaps.values()) {
                result = and(result, wellFormed(services.getTermBuilder().label(services.getTermBuilder().func(anonymisationFunction),
                                                         ParameterlessTermLabel.ANON_HEAP_LABEL)));
            }
            return result;
        }

        public Term buildAtMostOneFlagSetCondition()
        {
            final List<Term> notSetConditions = new LinkedList<Term>();
            notSetConditions.addAll(buildFlagsNotSetConditions(variables.breakFlags.values()));
            notSetConditions.addAll(buildFlagsNotSetConditions(variables.continueFlags.values()));
            if (variables.returnFlag != null) {
                notSetConditions.add(buildFlagNotSetCondition(variables.returnFlag));
            }
            notSetConditions.add(equals(var(variables.exception), NULL()));

            Term result = tt();
            for (Term notSetCondition : notSetConditions) {
                result = and(result, notSetCondition);
            }
            for (Term onlySetNotSetCondition : notSetConditions) {
                Term condition = not(onlySetNotSetCondition);
                for (Term notSetCondition : notSetConditions) {
                    if (notSetCondition != onlySetNotSetCondition) {
                        condition = and(condition, notSetCondition);
                    }
                }
                result = or(result, condition);
            }
            return result;
        }

        private List<Term> buildFlagsNotSetConditions(final Collection<ProgramVariable> flags)
        {
            final List<Term> result = new LinkedList<Term>();
            for (ProgramVariable flag : flags) {
                result.add(buildFlagNotSetCondition(flag));
            }
            return result;
        }

        private Term buildFlagNotSetCondition(final ProgramVariable flag)
        {
            return equals(var(flag), FALSE());
        }

    }

    /**
     * This class contains methods to add the premisses for the block contract rule to the goal.
     */
    protected final static class GoalsConfigurator {
        private final AbstractBlockContractBuiltInRuleApp application;
        private final TermLabelState termLabelState;
        private final Instantiation instantiation;
        private final List<Label> labels;
        private final BlockContract.Variables variables;
        private final PosInOccurrence occurrence;
        private final Services services;
        private final AbstractBlockContractRule rule;

        public GoalsConfigurator(final AbstractBlockContractBuiltInRuleApp application,
                                 final TermLabelState termLabelState,
                                 final Instantiation instantiation,
                                 final List<Label> labels,
                                 final BlockContract.Variables variables,
                                 final PosInOccurrence occurrence,
                                 final Services services,
                                 final AbstractBlockContractRule rule)
        {
            this.application = application;
            this.termLabelState = termLabelState;
            this.instantiation = instantiation;
            this.labels = labels;
            this.variables = variables;
            this.occurrence = occurrence;
            this.services = services;
            this.rule = rule;
        }

        public void setUpWdGoal(final Goal goal, final BlockContract contract,
                                final Term update, final Term anonUpdate,
                                final LocationVariable heap, final Function anonHeap,
                                final ImmutableSet<ProgramVariable> localIns) {
            if (goal == null) {
                return;
            }
            // FIXME: Handling of \old-references needs to be investigated,
            //        however only completeness is lost, soundness is guaranteed
            goal.setBranchLabel(WellDefinednessMacro.WD_BRANCH);
            final BlockWellDefinedness bwd = new BlockWellDefinedness(contract, localIns, services);
            services.getSpecificationRepository().addWdStatement(bwd);
            final LocationVariable heapAtPre = variables.remembranceHeaps.get(heap);
            final Term anon = anonHeap != null ? services.getTermBuilder().func(anonHeap) : null;
            final SequentFormula wdBlock =
                    bwd.generateSequent(variables.self, variables.exception,
                                        variables.result, heap, heapAtPre,
                                        anon, localIns, update, anonUpdate,
                                        services);
            goal.changeFormula(wdBlock, occurrence);
        }

        public void setUpValidityGoal(final Goal goal, final Term[] updates,
                                      final Term[] assumptions,
                                      final Term[] postconditions,
                                      final ProgramVariable exceptionParameter,
                                      final Terms terms) {
            goal.setBranchLabel("Validity");
            final TermBuilder tb = services.getTermBuilder();
            goal.addFormula(new SequentFormula(
                    tb.applySequential(updates, tb.and(assumptions))), true, false);
            final StatementBlock block =
                    new ValidityProgramConstructor(labels, instantiation.block,
                                                   variables, exceptionParameter,
                                                   services).construct();
            Statement wrappedBlock = wrapInMethodFrameIfContextIsAvailable(block);
            StatementBlock finishedBlock = finishTransactionIfModalityIsTransactional(wrappedBlock);
            JavaBlock newJavaBlock = JavaBlock.createJavaBlock(finishedBlock);
            Term newPost = tb.and(postconditions);
            newPost = AbstractOperationPO.addAdditionalUninterpretedPredicateIfRequired(services, newPost, ImmutableSLList.<LocationVariable>nil().prepend(terms.remembranceLocalVariables.keySet()), terms.exception);
            newPost = TermLabelManager.refactorTerm(termLabelState, services, null, newPost, rule, goal, BlockContractRule.NEW_POSTCONDITION_TERM_HINT, null);
            goal.changeFormula(new SequentFormula(
                  tb.applySequential(
                    updates,
                    tb.prog(instantiation.modality,
                            newJavaBlock, 
                            newPost,
                            TermLabelManager.instantiateLabels(termLabelState,
                                                               services, 
                                                               occurrence, 
                                                               application.rule(), 
                                                               application,
                                                               goal, 
                                                               BlockContractHint.
                                                               createValidityBranchHint(variables.exception),
                                                               null, 
                                                               instantiation.modality,
                                                               new ImmutableArray<Term>(newPost), 
                                                               null, 
                                                               newJavaBlock, 
                                                               instantiation.formula.getLabels())))),
                            occurrence);
            TermLabelManager.refactorGoal(termLabelState, services, occurrence, application.rule(), goal, null, null);
            final boolean oldInfFlowCheckInfoValue =
                    goal.getStrategyInfo(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY) != null &&
                    goal.getStrategyInfo(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY);
            StrategyInfoUndoMethod undo =
                    new StrategyInfoUndoMethod() {

                        @Override
                        public void undo(
                                de.uka.ilkd.key.util.properties.Properties strategyInfos) {
                            strategyInfos.put(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY,
                                              oldInfFlowCheckInfoValue);
                        }
                    };
            goal.addStrategyInfo(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY, false, undo);
        }

        private Statement wrapInMethodFrameIfContextIsAvailable(final StatementBlock block) {
            if (instantiation.context == null) {
                return block;
            }
            return new MethodFrame(null, instantiation.context, block);
        }

        private StatementBlock finishTransactionIfModalityIsTransactional(final Statement statement) {
            if (instantiation.isTransactional()) {
                return new StatementBlock(statement, new TransactionStatement(
                        de.uka.ilkd.key.java.recoderext.TransactionStatement.FINISH));
            }
            else {
                if (statement instanceof StatementBlock) {
                    return (StatementBlock) statement;
                }
                else {
                    return new StatementBlock(statement);
                }
            }
        }

        public void setUpPreconditionGoal(final Goal goal, final Term update,
                                          final Term[] preconditions) {
            final TermBuilder tb = services.getTermBuilder();
            goal.setBranchLabel("Precondition");
            Term fullPrecondition = tb.apply(update, tb.and(preconditions), null);
            fullPrecondition = TermLabelManager.refactorTerm(termLabelState, services, null, fullPrecondition, rule, goal, BlockContractRule.FULL_PRECONDITION_TERM_HINT, null);
            goal.changeFormula(new SequentFormula(fullPrecondition),
                               occurrence);
            TermLabelManager.refactorGoal(termLabelState, services, occurrence, application.rule(), goal, null, null);
        }

        public void setUpUsageGoal(final Goal goal, final Term[] updates,
                                   final Term[] assumptions) {
            final TermBuilder tb = services.getTermBuilder();
            goal.setBranchLabel("Usage");
            Term uAssumptions = tb.applySequential(updates, tb.and(assumptions));
            goal.addFormula(new SequentFormula(uAssumptions), true, false);
            goal.changeFormula(new SequentFormula(tb.applySequential(updates, buildUsageFormula(goal))),
                                                  occurrence);
            TermLabelManager.refactorGoal(termLabelState, services, occurrence, application.rule(), goal, null, null);
        }

        private Term buildUsageFormula(Goal goal)
        {
            return services.getTermBuilder().prog(
                instantiation.modality,
                replaceBlock(instantiation.formula.javaBlock(), instantiation.block,
                             constructAbruptTerminationIfCascade()),
                instantiation.formula.sub(0),
                TermLabelManager.instantiateLabels(termLabelState,
                                                   services, 
                                                   occurrence, 
                                                   application.rule(), 
                                                   application,
                                                   goal, 
                                                   BlockContractHint.USAGE_BRANCH,
                                                   null, 
                                                   instantiation.modality,
                                                   new ImmutableArray<Term>(instantiation.formula.sub(0)), 
                                                   null, 
                                                   instantiation.formula.javaBlock(), 
                                                   instantiation.formula.getLabels())
            );
        }

        private JavaBlock replaceBlock(final JavaBlock java, final StatementBlock oldBlock,
                                       final StatementBlock newBlock) {
            Statement newProgram = (Statement) new ProgramElementReplacer(java.program(), services)
                                                                       .replace(oldBlock, newBlock);
            return JavaBlock.createJavaBlock(newProgram instanceof StatementBlock ?
                    (StatementBlock) newProgram : new StatementBlock(newProgram));
        }

        private StatementBlock constructAbruptTerminationIfCascade() {
            List<If> ifCascade = new ArrayList<If>();
            for (Map.Entry<Label, ProgramVariable> flag : variables.breakFlags.entrySet()) {
                ifCascade.add(KeYJavaASTFactory.ifThen(flag.getValue(),
                        KeYJavaASTFactory.breakStatement(flag.getKey())));
            }
            for (Map.Entry<Label, ProgramVariable> flag : variables.continueFlags.entrySet()) {
                ifCascade.add(KeYJavaASTFactory.ifThen(flag.getValue(),
                        KeYJavaASTFactory.continueStatement(flag.getKey())));
            }
            if (variables.returnFlag != null) {
                ifCascade.add(KeYJavaASTFactory.ifThen(variables.returnFlag,
                        KeYJavaASTFactory.returnClause(variables.result)));
            }
            ifCascade.add(KeYJavaASTFactory.ifThen(
                new NotEquals(new ExtList(new Expression[] {variables.exception, NullLiteral.NULL})),
                KeYJavaASTFactory.throwClause(variables.exception)));
            return new StatementBlock(ifCascade.toArray(new Statement[ifCascade.size()]));
        }

    }
}
