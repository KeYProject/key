package de.uka.ilkd.key.rule;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.informationflow.proof.InfFlowCheckInfo;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.expression.operator.NotEquals;
import de.uka.ilkd.key.java.statement.Branch;
import de.uka.ilkd.key.java.statement.Break;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.Continue;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.TransactionStatement;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.java.visitor.OuterBreakContinueAndReturnCollector;
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
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.macros.WellDefinednessMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.StrategyInfoUndoMethod;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.rule.AbstractBlockContractRule.BlockContractHint;
import de.uka.ilkd.key.rule.AbstractBlockSpecificationElementRule.Instantiation;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.BlockSpecificationElement;
import de.uka.ilkd.key.speclang.BlockSpecificationElement.Variables;
import de.uka.ilkd.key.speclang.BlockWellDefinedness;
import de.uka.ilkd.key.speclang.LoopContract;
import de.uka.ilkd.key.util.LinkedHashMap;
import de.uka.ilkd.key.util.MiscTools;

/**
 * This contains various builders used in building formulae and terms for block and loop contracts.
 */
public final class BlockContractBuilders {

    public static final String ANON_IN_PREFIX = "anonIn_";
    public static final String ANON_OUT_PREFIX = "anonOut_";

    private BlockContractBuilders() { }

    /**
     * This class is used to construct {@code block'} from {@code block} (see Wacker 2012, 3.3).
     *
     * @see ValidityProgramConstructor#construct()
     */
    public static final class ValidityProgramConstructor {

        private final Iterable<Label> labels;
        private final StatementBlock block;
        private final BlockContract.Variables variables;
        private final BlockContract.Variables alreadyDeclared;
        private final Services services;
        private final List<Statement> statements;
        private final ProgramVariable exceptionParameter;

        public ValidityProgramConstructor(final Iterable<Label> labels,
                                          final StatementBlock block,
                                          final BlockContract.Variables variables,
                                          final ProgramVariable exceptionParameter,
                                          final Services services) {
            this(labels, block, variables, exceptionParameter, services, null);
        }

        public ValidityProgramConstructor(final Iterable<Label> labels,
                                          final StatementBlock block,
                                          final BlockContract.Variables variables,
                                          final ProgramVariable exceptionParameter,
                                          final Services services,
                                          final BlockContract.Variables alreadyDeclared) {
            this.labels = labels;
            this.block = block;
            this.variables = variables;
            this.services = services;
            this.exceptionParameter = exceptionParameter;
            statements = new LinkedList<Statement>();
            this.alreadyDeclared = alreadyDeclared;
        }

        public StatementBlock construct() {
            declareFlagsFalse();
            declareResultDefault();
            declareExceptionNull();
            executeBlockSafely();
            return new StatementBlock(statements.toArray(new Statement[statements.size()]));
        }

        private void declareFlagsFalse() {
            for (ProgramVariable flag : variables.breakFlags.values()) {
                if (alreadyDeclared != null
                      && alreadyDeclared.breakFlags.containsValue(flag)) {
                    statements.add(KeYJavaASTFactory.assign(flag, BooleanLiteral.FALSE));
                } else {
                    statements.add(KeYJavaASTFactory.declare(flag, BooleanLiteral.FALSE,
                            services.getJavaInfo().getKeYJavaType("boolean")));
                }
            }

            for (ProgramVariable flag : variables.continueFlags.values()) {
                if (alreadyDeclared != null
                      && alreadyDeclared.continueFlags.containsValue(flag)) {
                    statements.add(KeYJavaASTFactory.assign(flag, BooleanLiteral.FALSE));
                } else {
                    statements.add(KeYJavaASTFactory.declare(flag, BooleanLiteral.FALSE,
                            services.getJavaInfo().getKeYJavaType("boolean")));
                }
            }
            if (variables.returnFlag != null) {
                if (alreadyDeclared != null && alreadyDeclared.returnFlag != null) {
                    statements.add(KeYJavaASTFactory.assign(variables.returnFlag,
                                                            BooleanLiteral.FALSE));
                } else {
                    statements.add(KeYJavaASTFactory.declare(variables.returnFlag,
                                                             BooleanLiteral.FALSE,
                                   services.getJavaInfo().getKeYJavaType("boolean")));
                }
            }
        }

        private void declareResultDefault() {
            if (occursReturnAndIsReturnTypeNotVoid()) {
                if (alreadyDeclared != null && alreadyDeclared.result != null) {
                    KeYJavaType resultType = variables.result.getKeYJavaType();
                    statements.add(KeYJavaASTFactory.assign(
                            variables.result, resultType.getDefaultValue()));
                } else {
                    KeYJavaType resultType = variables.result.getKeYJavaType();
                    statements.add(KeYJavaASTFactory.declare(
                            variables.result, resultType.getDefaultValue(), resultType));
                }
            }
        }

        private boolean occursReturnAndIsReturnTypeNotVoid() {
            return variables.returnFlag != null && variables.result != null;
        }

        private void declareExceptionNull() {
            if (alreadyDeclared != null && alreadyDeclared.exception != null) {
                statements.add(KeYJavaASTFactory.assign(
                        variables.exception, NullLiteral.NULL));
            } else {
                statements.add(KeYJavaASTFactory.declare(
                        variables.exception, NullLiteral.NULL,
                        variables.exception.getKeYJavaType()));
            }
        }

        private void executeBlockSafely() {
            final Label breakOutLabel = new ProgramElementName("breakOut");
            final StatementBlock almostSafeBlock =
                    replaceOuterBreaksContinuesAndReturns(block, breakOutLabel);
            final Statement labeledAlmostSafeBlock = label(almostSafeBlock, labels);
            final Statement safeStatement = wrapInTryCatch(labeledAlmostSafeBlock,
                                                           exceptionParameter);
            statements.add(new LabeledStatement(breakOutLabel, safeStatement,
                                                PositionInfo.UNDEFINED));
        }

        private Statement label(final StatementBlock block, Iterable<Label> labels) {
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
                                                  new StatementBlock(
                                                      KeYJavaASTFactory.assign(
                                                          variables.exception,
                                                          exceptionParameter)));
            return new Try(new StatementBlock(labeldBlock), new Branch[] {katch});
        }
    }

    /**
     * This class contains methods to create new variables from the contract's
     * placeholder variables
     * (see {@link BlockContract#getPlaceholderVariables()}), and register them.
     */
    public static final class VariablesCreatorAndRegistrar {

        private final Goal goal;
        private final BlockContract.Variables placeholderVariables;
        private final TermServices services;

        /**
         *
         * @param goal If this is not null, all created variables are added to it.
         *        If it is null, the variables are instead added to the {@code services}' namespace.
         * @param placeholderVariables the placeholders from which to create the variables.
         * @param services
         */
        public VariablesCreatorAndRegistrar(final Goal goal,
                                            final BlockContract.Variables placeholderVariables,
                                            final TermServices services) {
            this.goal = goal;
            this.placeholderVariables = placeholderVariables;
            this.services = services;
        }

        public Variables createAndRegister(Term self, boolean existingPO) {
            if (existingPO) {
                // In an existing PO, the outer remembrance vars already exist and refer to the
                // current method's prestate.
                return new BlockContract.Variables(
                    placeholderVariables.self,
                    createAndRegisterFlags(placeholderVariables.breakFlags),
                    createAndRegisterFlags(placeholderVariables.continueFlags),
                    createAndRegisterVariable(placeholderVariables.returnFlag),
                    createAndRegisterVariable(placeholderVariables.result),
                    createAndRegisterVariable(placeholderVariables.exception),
                    createAndRegisterRemembranceVariables(placeholderVariables.remembranceHeaps),
                    createAndRegisterRemembranceVariables(
                            placeholderVariables.remembranceLocalVariables),
                    placeholderVariables.outerRemembranceHeaps,
                    placeholderVariables.outerRemembranceVariables,
                    services);
            } else {
                // In a new PO, the outer remembrance vars don't exist yet.
                return new BlockContract.Variables(
                    self != null ? self.op(ProgramVariable.class) : null,
                    createAndRegisterFlags(placeholderVariables.breakFlags),
                    createAndRegisterFlags(placeholderVariables.continueFlags),
                    createAndRegisterVariable(placeholderVariables.returnFlag),
                    createAndRegisterVariable(placeholderVariables.result),
                    createAndRegisterVariable(placeholderVariables.exception),
                    createAndRegisterRemembranceVariables(placeholderVariables.remembranceHeaps),
                    createAndRegisterRemembranceVariables(
                            placeholderVariables.remembranceLocalVariables),
                    createAndRegisterRemembranceVariables(
                            placeholderVariables.outerRemembranceHeaps),
                    createAndRegisterRemembranceVariables(
                            placeholderVariables.outerRemembranceVariables),
                    services);
            }
        }

        /**
         * Creates and registers copies of the remembrance variables and heaps.
         *
         * @param suffix a suffix for the new variables' names.
         * @return a {@link Variables} object containing the new {@link ProgramVariables}.
         */
        public Variables createAndRegisterCopies(String suffix) {
            return new BlockContract.Variables(
                    null,
                    placeholderVariables.breakFlags,
                    placeholderVariables.continueFlags,
                    placeholderVariables.returnFlag,
                    placeholderVariables.result,
                    placeholderVariables.exception,
                    createAndRegisterRemembranceVariables(
                            appendSuffix(placeholderVariables.remembranceHeaps, suffix)),
                    createAndRegisterRemembranceVariables(
                            appendSuffix(placeholderVariables.remembranceLocalVariables, suffix)),
                    placeholderVariables.outerRemembranceHeaps,
                    placeholderVariables.outerRemembranceVariables,
                    services);
        }

        private <K> Map<K, LocationVariable> appendSuffix(
                final Map<K, LocationVariable> map,
                final String suffix) {
            final Map<K, LocationVariable> result = new LinkedHashMap<>();

            for (Entry<K, LocationVariable> entry : map.entrySet()) {
                K key = entry.getKey();
                LocationVariable value = entry.getValue();

                String newName = services.getTermBuilder().newName(
                        value.name().toString() + suffix);
                LocationVariable newValue =
                        new LocationVariable(new ProgramElementName(newName),
                                             value.getKeYJavaType());

                result.put(key, newValue);
            }

            return result;
        }

        private Map<Label, ProgramVariable>
                    createAndRegisterFlags(final Map<Label,
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

        private LocationVariable
                    createAndRegisterVariable(final ProgramVariable placeholderVariable) {
            if (placeholderVariable != null) {
                String newName =
                    services.getTermBuilder().newName(placeholderVariable.name().toString());
                LocationVariable newVariable =
                        new LocationVariable(new ProgramElementName(newName),
                                             placeholderVariable.getKeYJavaType());

                if (goal != null) {
                    goal.addProgramVariable(newVariable);
                } else {
                    Namespace<IProgramVariable> progVarNames =
                        services.getNamespaces().programVariables();
                    if (newVariable != null
                          && progVarNames.lookup(placeholderVariable.name()) == null) {
                        progVarNames.addSafely(newVariable);
                    }
                }

                return newVariable;
            } else {
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

        public Term buildOuterRemembranceUpdate() {
            Term result = skip();

            for (LocationVariable var : variables.outerRemembranceVariables.keySet()) {
                final Term update =
                    elementary(variables.outerRemembranceVariables.get(var), var(var));
                result = parallel(result, update);
            }

            return result;
        }

        public Term buildAnonOutUpdate(final Map<LocationVariable, Function> anonymisationHeaps,
                                             final Map<LocationVariable, Term> modifiesClauses) {
            Term result = buildLocalVariablesAnonOutUpdate();
            for (Map.Entry<LocationVariable, Function> anonymisationHeap
                    : anonymisationHeaps.entrySet()) {
                Term anonymisationUpdate = skip();
                final Term modifiesClause = modifiesClauses.get(anonymisationHeap.getKey());
                if (!modifiesClause.equals(strictlyNothing())) {
                    anonymisationUpdate =
                        anonUpd(anonymisationHeap.getKey(), modifiesClause,
                                services.getTermBuilder().label(
                                    services.getTermBuilder()
                                        .func(anonymisationHeap.getValue()),
                                    ParameterlessTermLabel.ANON_HEAP_LABEL));
                }
                result = parallel(result, anonymisationUpdate);
            }
            return result;
        }

        public Term buildAnonOutUpdate(final ProgramElement el,
                                       final Map<LocationVariable, Function> anonymisationHeaps,
                                       final Map<LocationVariable, Term> modifiesClauses) {
            Set<LocationVariable> vars = new LinkedHashSet<>();
            for (ProgramVariable var : MiscTools.getLocalOuts(el, services)) {
                if (var instanceof LocationVariable) {
                    vars.add((LocationVariable) var);
                }
            }

            Term result = buildLocalVariablesAnonUpdate(vars, ANON_OUT_PREFIX);
            for (Map.Entry<LocationVariable, Function> anonymisationHeap
                    : anonymisationHeaps.entrySet()) {
                Term anonymisationUpdate = skip();
                final Term modifiesClause = modifiesClauses.get(anonymisationHeap.getKey());
                if (!modifiesClause.equals(strictlyNothing())) {
                    anonymisationUpdate =
                        anonUpd(anonymisationHeap.getKey(), modifiesClause,
                                services.getTermBuilder().label(
                                    services.getTermBuilder()
                                        .func(anonymisationHeap.getValue()),
                                    ParameterlessTermLabel.ANON_HEAP_LABEL));
                }
                result = parallel(result, anonymisationUpdate);
            }
            return result;
        }

        public Term buildAnonInUpdate(final Map<LocationVariable, Function> anonymisationHeaps) {
            Term result = buildLocalVariablesAnonInUpdate();

            for (Map.Entry<LocationVariable, Function> anonymisationHeap
                    : anonymisationHeaps.entrySet()) {
                Term anonymisationUpdate = skip();

                anonymisationUpdate = anonUpd(anonymisationHeap.getKey(), allLocs(),
                        services.getTermBuilder().label(
                                services.getTermBuilder().func(anonymisationHeap.getValue()),
                                ParameterlessTermLabel.ANON_HEAP_LABEL));

                result = parallel(result, anonymisationUpdate);
            }

            return result;
        }

        private Term buildLocalVariablesAnonOutUpdate() {
            return buildLocalVariablesAnonUpdate(variables.remembranceLocalVariables.keySet(),
                    ANON_OUT_PREFIX);
        }

        private Term buildLocalVariablesAnonInUpdate() {

            return buildLocalVariablesAnonUpdate(variables.outerRemembranceVariables.keySet(),
                    ANON_IN_PREFIX);
        }

        private Term buildLocalVariablesAnonUpdate(Collection<LocationVariable> vars,
                                                   String prefix) {
            Term result = skip();

            for (LocationVariable variable : vars) {
                final String anonymisationName = newName(prefix + variable.name());
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

        protected final BlockContract.Terms terms;

        private final BlockSpecificationElement contract;
        private final List<LocationVariable> heaps;
        private final BlockContract.Variables variables;

        public ConditionsAndClausesBuilder(final BlockSpecificationElement contract,
                                           final List<LocationVariable> heaps,
                                           final BlockContract.Variables variables,
                                           final Term self, final Services services) {
            super(services.getTermFactory(), services);
            this.contract = contract;
            this.heaps = heaps;
            this.variables = variables;
            this.terms = variables.termify(self);
        }

        public BlockSpecificationElement.Terms getTerms() {
            return terms;
        }

        public Term buildPrecondition() {
            Term result = tt();

            for (LocationVariable heap : heaps) {
                result = and(result,
                             contract.getPrecondition(heap, getBaseHeap(), terms, services));
            }

            return result;
        }

        public Term buildWellFormedHeapsCondition() {
            Term result = tt();
            for (LocationVariable heap : heaps) {
                result = and(result, wellFormed(heap));
            }
            return result;
        }

        public Term buildReachableInCondition(
                final ImmutableSet<ProgramVariable> localInVariables) {
            return buildReachableCondition(localInVariables);
        }

        public Term buildReachableOutCondition(
                final ImmutableSet<ProgramVariable> localOutVariables) {
            final Term reachableResult =
                    (variables.result != null) ?
                    reachableValue(variables.result) : services.getTermBuilder().tt();
            return and(
                buildReachableCondition(localOutVariables),
                reachableResult,
                reachableValue(variables.exception)
            );
        }

        public Term buildReachableCondition(final ImmutableSet<ProgramVariable> variables) {
            Term result = tt();
            for (ProgramVariable variable : variables) {
                result = and(result, reachableValue(variable));
            }
            return result;
        }

        public Map<LocationVariable, Term> buildModifiesClauses() {
            Map<LocationVariable, Term> result = new LinkedHashMap<LocationVariable, Term>();
            for (final LocationVariable heap : heaps) {
                result.put(heap, contract.getModifiesClause(heap, var(heap),
                                                            terms.self, services));
            }
            return result;
        }

        public Term buildDecreasesCheck() {
            if (!(contract instanceof LoopContract)) {
                throw new IllegalStateException();
            }

            LoopContract lc = (LoopContract) contract;
            Term decreases = lc.getDecreases();

            if (decreases == null) {
                return tt();
            }

            Term oldDecreases =
                    new OpReplacer(
                            variables.combineRemembranceVariables(),
                            services.getTermFactory())
                    .replace(decreases);

            // The condition (decreases >= 0) is part of the precondition
            // and does not need to be repeated here.
            return lt(decreases, oldDecreases);
        }

        public Term buildPostcondition() {
            Term result = tt();
            for (LocationVariable heap : heaps) {
                result = and(result, contract.getPostcondition(heap, getBaseHeap(),
                                                               terms, services));
            }
            return result;
        }

        public Term buildFrameCondition(final Map<LocationVariable, Term> modifiesClauses) {
            Term result = tt();
            Map<LocationVariable, Map<Term, Term>> remembranceVariables =
                    constructRemembranceVariables();
            for (LocationVariable heap : heaps) {
                final Term modifiesClause = modifiesClauses.get(heap);
                final Term frameCondition;
                if (modifiesClause.equals(strictlyNothing())) {
                    frameCondition =
                        frameStrictlyEmpty(var(heap), remembranceVariables.get(heap));
                } else {
                    frameCondition =
                        frame(var(heap), remembranceVariables.get(heap), modifiesClause);
                }
                result = and(result, frameCondition);
            }
            return result;
        }

        private Map<LocationVariable, Map<Term, Term>> constructRemembranceVariables() {
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

        private LocationVariable getBaseHeapFunction() {
            return services.getTypeConverter().getHeapLDT().getHeap();
        }

        public Term buildWellFormedAnonymisationHeapsCondition(
                final Map<LocationVariable, Function> anonymisationHeaps) {
            Term result = tt();
            for (Function anonymisationFunction : anonymisationHeaps.values()) {
                result =
                    and(result,
                        wellFormed(
                            services.getTermBuilder().label(
                                services.getTermBuilder().func(anonymisationFunction),
                                ParameterlessTermLabel.ANON_HEAP_LABEL)));
            }
            return result;
        }

        public Term buildAtMostOneFlagSetCondition() {
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


        /**
         * Builds the assumptions for the {@code self} variable
         * ({@code self != null & self.created == true & exactInstance(self)})
         *
         * @param heaps
         * @param pm
         * @param selfVar
         * @param services
         * @return
         */
        public Term buildSelfConditions(List<LocationVariable> heaps, IProgramMethod pm,
                KeYJavaType selfKJT,
                Term self, Services services) {
            if (self != null && !pm.isConstructor()) {
                Term notNull = not(equals(self, NULL()));

                Term created = null;
                for (LocationVariable heap : heaps) {
                    if (heap == services.getTypeConverter().getHeapLDT().getSavedHeap()) {
                        continue;
                    }
                    final Term cr = created(var(heap), self);
                    if (created == null) {
                        created = cr;
                    } else {
                        created = and(created, cr);
                    }
                }

                Term exactType = exactInstance(selfKJT.getSort(), self);

                return or(notNull, created, exactType);
            } else {
                return tt();
            }
        }

        private List<Term> buildFlagsNotSetConditions(final Collection<ProgramVariable> flags) {
            final List<Term> result = new LinkedList<Term>();
            for (ProgramVariable flag : flags) {
                result.add(buildFlagNotSetCondition(flag));
            }
            return result;
        }

        private Term buildFlagNotSetCondition(final ProgramVariable flag) {
            return equals(var(flag), FALSE());
        }
    }

    /**
     * This class contains methods to add the premisses for the block contract rule to the goal.
     */
    public final static class GoalsConfigurator {
        private final AbstractBlockSpecificationElementBuiltInRuleApp application;
        private final TermLabelState termLabelState;
        private final Instantiation instantiation;
        private final List<Label> labels;
        private final BlockSpecificationElement.Variables variables;
        private final PosInOccurrence occurrence;
        private final Services services;
        private final AbstractBlockSpecificationElementRule rule;

        public GoalsConfigurator(final AbstractBlockSpecificationElementBuiltInRuleApp
                                     application,
                                 final TermLabelState termLabelState,
                                 final Instantiation instantiation,
                                 final List<Label> labels,
                                 final BlockSpecificationElement.Variables variables,
                                 final PosInOccurrence occurrence,
                                 final Services services,
                                 final AbstractBlockSpecificationElementRule rule) {
            this.application = application;
            this.termLabelState = termLabelState;
            this.instantiation = instantiation;
            this.labels = labels;
            this.variables = variables;
            this.occurrence = occurrence;
            this.services = services;
            this.rule = rule;
        }

        /**
         *
         * @param goal If this is not {@code null}, the returned formula is added to this goal.
         * @param contract
         * @param update
         * @param anonUpdate
         * @param heap
         * @param anonHeap
         * @param localIns
         * @return the well-definedness formula.
         */
        public Term setUpWdGoal(final Goal goal, final BlockContract contract,
                                final Term update, final Term anonUpdate,
                                final LocationVariable heap, final Function anonHeap,
                                final ImmutableSet<ProgramVariable> localIns) {
            // FIXME: Handling of \old-references needs to be investigated,
            //        however only completeness is lost, soundness is guaranteed
            final BlockWellDefinedness bwd =
                new BlockWellDefinedness(contract, variables, localIns, services);
            services.getSpecificationRepository().addWdStatement(bwd);
            final LocationVariable heapAtPre = variables.remembranceHeaps.get(heap);
            final Term anon =
                anonHeap != null ? services.getTermBuilder().func(anonHeap) : null;
            final SequentFormula wdBlock =
                    bwd.generateSequent(variables.self, variables.exception,
                                        variables.result, heap, heapAtPre,
                                        anon, localIns, update, anonUpdate,
                                        services);

            if (goal != null) {
                goal.setBranchLabel(WellDefinednessMacro.WD_BRANCH);
                goal.changeFormula(wdBlock, occurrence);
            }

            return wdBlock.formula();
        }

        /**
         *
         * @param goal If this is not {@code null}, the returned term is added to this goal.
         * @param updates
         * @param assumptions
         * @param postconditions
         * @param exceptionParameter
         * @param terms
         * @return the term for the validity goal.
         */
        public Term setUpValidityGoal(final Goal goal, final Term[] updates,
                                      final Term[] assumptions,
                                      final Term[] postconditions,
                                      final ProgramVariable exceptionParameter,
                                      final BlockSpecificationElement.Terms terms) {
            final TermBuilder tb = services.getTermBuilder();
            final StatementBlock block =
                    new ValidityProgramConstructor(labels, instantiation.block,
                                                   variables, exceptionParameter,
                                                   services).construct();
            Statement wrappedBlock = wrapInMethodFrameIfContextIsAvailable(block);
            StatementBlock finishedBlock =
                finishTransactionIfModalityIsTransactional(wrappedBlock);
            JavaBlock newJavaBlock = JavaBlock.createJavaBlock(finishedBlock);
            Term newPost = tb.and(postconditions);
            newPost = AbstractOperationPO.addAdditionalUninterpretedPredicateIfRequired(
                    services,
                    newPost,
                    ImmutableSLList.<LocationVariable>nil()
                        .prepend(terms.remembranceLocalVariables.keySet()),
                    terms.exception);
            newPost = TermLabelManager.refactorTerm(
                    termLabelState,
                    services,
                    null,
                    newPost,
                    rule,
                    goal,
                    AbstractBlockSpecificationElementRule.NEW_POSTCONDITION_TERM_HINT,
                    null);


            Term term;

            if (goal != null) {
                goal.setBranchLabel("Validity");
                goal.addFormula(new SequentFormula(
                        tb.applySequential(updates, tb.and(assumptions))), true, false);

                ImmutableArray<TermLabel> labels =
                    TermLabelManager.instantiateLabels(
                        termLabelState, services, occurrence,
                        application.rule(), application, goal,
                        BlockContractHint.createValidityBranchHint(variables.exception),
                        null, instantiation.modality,
                        new ImmutableArray<Term>(newPost),
                        null, newJavaBlock,
                        instantiation.formula.getLabels());

                term = tb.applySequential(updates,
                                          tb.prog(instantiation.modality,
                                                  newJavaBlock,
                                                  newPost,
                                                  labels));

                goal.changeFormula(new SequentFormula(term), occurrence);
                TermLabelManager.refactorGoal(termLabelState, services, occurrence,
                                              application.rule(), goal, null, null);
                final boolean oldInfFlowCheckInfoValue =
                        goal.getStrategyInfo(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY) != null
                          && goal.getStrategyInfo(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY);
                StrategyInfoUndoMethod undo =
                    new StrategyInfoUndoMethod() {
                        @Override
                        public void undo(
                            de.uka.ilkd.key.util.properties.Properties
                                strategyInfos) {
                            strategyInfos.put(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY,
                                              oldInfFlowCheckInfoValue);
                        }
                    };
                goal.addStrategyInfo(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY, false, undo);
            } else {
                Term pre = tb.and(assumptions);
                Term prog =
                    tb.prog(instantiation.modality, newJavaBlock,
                            newPost, new ImmutableArray<>());
                term = tb.applySequential(updates, tb.imp(pre, prog));
            }

            return term;
        }

        public Term setUpLoopValidityGoal(final Goal goal,
                final LoopContract contract,
                final Term context,
                final Term remember,
                final Term rememberNext,
                final Map<LocationVariable, Function> anonOutHeaps,
                final Map<LocationVariable, Term> modifiesClauses,
                final Term[] assumptions,
                final Term decreasesCheck,
                final Term[] postconditions,
                final Term[] postconditionsNext,
                final ProgramVariable exceptionParameter,
                final BlockSpecificationElement.Terms terms,
                final BlockSpecificationElement.Variables nextVars) {
            final TermBuilder tb = services.getTermBuilder();
            final Modality modality = instantiation.modality;

            ProgramVariable conditionVariable = AbstractBlockSpecificationElementRule
                    .createLocalVariable("cond",
                            services.getJavaInfo().getKeYJavaType("boolean"),
                            services);

            ProgramVariable brokeLoopVariable = AbstractBlockSpecificationElementRule
                    .createLocalVariable("brokeLoop",
                            services.getJavaInfo().getKeYJavaType("boolean"),
                            services);

            ProgramVariable continuedLoopVariable = AbstractBlockSpecificationElementRule
                    .createLocalVariable("continuedLoop",
                            services.getJavaInfo().getKeYJavaType("boolean"),
                            services);

            OuterBreakContinueAndReturnCollector collector =
                    new OuterBreakContinueAndReturnCollector(contract.getBody(),
                            new LinkedList<>(), services);

            List<Break> bodyBreaks = collector.getBreaks();
            List<Continue> bodyContinues = collector.getContinues();
            collector.collect();

            boolean bodyBreakFound = false;

            Map<Label, ProgramVariable> breakFlags =
                new LinkedHashMap<>(variables.breakFlags);
            for (Break br : bodyBreaks) {
                Label label = br.getLabel();
                if (label == null || contract.getLoopLabels().contains(label)) {
                    breakFlags.put(label, brokeLoopVariable);
                    bodyBreakFound = true;
                }
            }

            Map<Label, ProgramVariable> continueFlags =
                    new LinkedHashMap<>(variables.continueFlags);
            continueFlags.remove(null);
            for (Continue cont : bodyContinues) {
                Label label = cont.getLabel();
                if (label == null || contract.getLoopLabels().contains(label)) {
                    continueFlags.put(label, continuedLoopVariable);
                }
            }

            BlockSpecificationElement.Variables bodyVariables = new Variables(
                    variables.self,
                    breakFlags,
                    continueFlags,
                    variables.returnFlag,
                    variables.result,
                    variables.exception,
                    variables.remembranceHeaps,
                    variables.remembranceLocalVariables,
                    variables.outerRemembranceHeaps,
                    variables.outerRemembranceVariables,
                    services);


            JavaBlock unfold =
                    JavaBlock.createJavaBlock(new StatementBlock(
                            wrapInMethodFrameIfContextIsAvailable(
                                    new ValidityProgramConstructor(
                                            labels,
                                            new StatementBlock(
                                                    KeYJavaASTFactory.declare(
                                                            conditionVariable,
                                                            contract.getGuard())),
                                            variables,
                                            exceptionParameter,
                                            services)
                                    .construct())));

            JavaBlock body =
                    JavaBlock.createJavaBlock(new StatementBlock(
                            wrapInMethodFrameIfContextIsAvailable(
                                    new ValidityProgramConstructor(
                                            labels,
                                            contract.getBody(),
                                            bodyVariables,
                                            exceptionParameter,
                                            services,
                                            variables)
                                    .construct())));

            JavaBlock tail =
                    JavaBlock.createJavaBlock(new StatementBlock(
                            finishTransactionIfModalityIsTransactional(
                            wrapInMethodFrameIfContextIsAvailable(
                                    new ValidityProgramConstructor(
                                            labels,
                                            contract.getTail(),
                                            variables,
                                            exceptionParameter,
                                            services,
                                            variables)
                                    .construct()))));

            Term anonOut = new UpdatesBuilder(variables, services)
                    .buildAnonOutUpdate(contract.getLoop(), anonOutHeaps, modifiesClauses);

            Term post = tb.and(postconditions);
            post = AbstractOperationPO.addAdditionalUninterpretedPredicateIfRequired(
                    services,
                    post,
                    ImmutableSLList.<LocationVariable>nil()
                        .prepend(terms.remembranceLocalVariables.keySet()),
                    terms.exception);
            post = TermLabelManager.refactorTerm(
                    termLabelState,
                    services,
                    null,
                    post,
                    rule,
                    goal,
                    AbstractBlockSpecificationElementRule.NEW_POSTCONDITION_TERM_HINT,
                    null);

            Term postNext = tb.and(postconditionsNext);
            postNext = AbstractOperationPO.addAdditionalUninterpretedPredicateIfRequired(
                    services,
                    postNext,
                    ImmutableSLList.<LocationVariable>nil()
                        .prepend(terms.remembranceLocalVariables.keySet()),
                    terms.exception);
            postNext = TermLabelManager.refactorTerm(
                    termLabelState,
                    services,
                    null,
                    postNext,
                    rule,
                    goal,
                    AbstractBlockSpecificationElementRule.NEW_POSTCONDITION_TERM_HINT,
                    null);

            Term postAfterTail = tb.prog(modality, tail, post);
            Term pre = tb.and(assumptions);
            Term brokeLoop = tb.equals(tb.var(brokeLoopVariable), tb.TRUE());
            Term notBrokeLoop = tb.not(brokeLoop);
            Term exceptionEqNull = tb.equals(tb.var(variables.exception), tb.NULL());
            Term exceptionNeqNull = tb.not(exceptionEqNull);
            Term cond = tb.equals(tb.var(conditionVariable), tb.TRUE());
            Term notCond = tb.not(cond);

            Set<Term> abruptTerms = new LinkedHashSet<>();
            abruptTerms.add(exceptionNeqNull);
            if (terms.returnFlag != null) {
                abruptTerms.add(tb.equals(terms.returnFlag, tb.TRUE()));
            }
            for (Term term : terms.continueFlags.values()) {
                abruptTerms.add(tb.equals(term, tb.TRUE()));
            }
            for (Term term : terms.breakFlags.values()) {
                abruptTerms.add(tb.equals(term, tb.TRUE()));
            }

            Term abrupt = tb.or(abruptTerms);
            Term notAbrupt = tb.not(abrupt);

            // Add a simplified version of the formula if tail is empty.
            Term term;
            if (contract.getTail().isEmpty()) {
                Term postBody;
                if (bodyBreakFound) {
                    postBody = tb.and(
                        tb.imp(tb.or(brokeLoop, abrupt), post),
                        tb.imp(tb.and(notBrokeLoop, notAbrupt),
                               tb.and(pre, decreasesCheck,
                                      tb.apply(rememberNext,
                                               tb.apply(anonOut,
                                                        tb.imp(postNext, post)
                        )))));
                } else {
                    postBody =
                        tb.and(tb.imp(abrupt, post),
                               tb.imp(notAbrupt,
                                      tb.and(pre, decreasesCheck,
                                             tb.apply(rememberNext,
                                                      tb.apply(anonOut,
                                                               tb.imp(postNext, post)
                        )))));
                }

                term = tb.apply(context,
                    tb.imp(pre,
                        tb.apply(remember, tb.prog(modality, unfold, tb.and(
                            tb.imp(tb.or(exceptionNeqNull, notCond), post),
                            tb.imp(tb.and(exceptionEqNull, cond),
                                tb.prog(modality, body, postBody))
                            )
                        ))
                    )
                );
            } else {
                Term postBody;
                if (bodyBreakFound) {
                    postBody =
                        tb.and(tb.imp(brokeLoop, postAfterTail),
                               tb.imp(abrupt, post),
                               tb.imp(tb.and(notBrokeLoop, notAbrupt),
                                   tb.and(pre, decreasesCheck,
                                          tb.apply(rememberNext,
                                              tb.apply(anonOut,
                                                  tb.and(tb.imp(abrupt,
                                                             tb.imp(postNext,
                                                                 post)),
                                                         tb.imp(notAbrupt,
                                                             tb.prog(modality, tail,
                                                                 tb.imp(postNext, post)))
                            )
                        ))))
                    );
                } else {
                    postBody =
                        tb.and(tb.imp(abrupt, post),
                               tb.imp(notAbrupt,
                                   tb.and(pre, decreasesCheck,
                                          tb.apply(rememberNext,
                                              tb.apply(anonOut,
                                                  tb.and(tb.imp(abrupt,
                                                             tb.imp(postNext, post)),
                                                         tb.imp(notAbrupt,
                                                             tb.prog(modality, tail,
                                                                 tb.imp(postNext, post)))
                            )
                        ))))
                    );
                }

                term = tb.apply(context,
                    tb.imp(pre,
                        tb.apply(remember, tb.prog(modality, unfold, tb.and(
                            tb.imp(exceptionNeqNull, post),
                            tb.imp(tb.and(exceptionEqNull, notCond), postAfterTail),
                            tb.imp(tb.and(exceptionEqNull, cond),
                                tb.prog(modality, body, postBody)
                            )
                        )
                    )))
                );
            }

            if (goal != null) {
                goal.setBranchLabel("Validity");

                final boolean oldInfFlowCheckInfoValue =
                        goal.getStrategyInfo(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY) != null
                          && goal.getStrategyInfo(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY);
                StrategyInfoUndoMethod undo =
                    new StrategyInfoUndoMethod() {
                        @Override
                        public void undo(
                            de.uka.ilkd.key.util.properties.Properties
                                strategyInfos) {
                            strategyInfos.put(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY,
                                              oldInfFlowCheckInfoValue);
                        }
                    };
                goal.addStrategyInfo(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY, false, undo);

                goal.changeFormula(new SequentFormula(term), occurrence);
            }

            return term;
        }

        private Statement wrapInMethodFrameIfContextIsAvailable(final StatementBlock block) {
            if (instantiation.context == null) {
                return block;
            }
            return new MethodFrame(null, instantiation.context, block);
        }

        private StatementBlock
                    finishTransactionIfModalityIsTransactional(final Statement statement) {
            if (instantiation.isTransactional()) {
                return new StatementBlock(statement, new TransactionStatement(
                        de.uka.ilkd.key.java.recoderext.TransactionStatement.FINISH));
            } else {
                if (statement instanceof StatementBlock) {
                    return (StatementBlock) statement;
                } else {
                    return new StatementBlock(statement);
                }
            }
        }

        public void setUpPreconditionGoal(final Goal goal, final Term update,
                                          final Term[] preconditions) {
            final TermBuilder tb = services.getTermBuilder();
            goal.setBranchLabel("Precondition");
            Term fullPrecondition = tb.apply(update, tb.and(preconditions), null);
            fullPrecondition =
                TermLabelManager
                    .refactorTerm(termLabelState, services, null,
                                  fullPrecondition, rule, goal,
                                  BlockContractInternalRule.FULL_PRECONDITION_TERM_HINT,
                                  null);
            goal.changeFormula(new SequentFormula(fullPrecondition),
                               occurrence);
            TermLabelManager.refactorGoal(termLabelState, services, occurrence,
                                          application.rule(), goal, null, null);
        }

        public void setUpUsageGoal(final Goal goal, final Term[] updates,
                                   final Term[] assumptions) {
            final TermBuilder tb = services.getTermBuilder();
            goal.setBranchLabel("Usage");
            Term uAssumptions = tb.applySequential(updates, tb.and(assumptions));
            goal.addFormula(new SequentFormula(uAssumptions), true, false);
            goal.changeFormula(new SequentFormula(tb.applySequential(updates,
                                                      buildUsageFormula(goal))),
                                                  occurrence);
            TermLabelManager.refactorGoal(termLabelState, services, occurrence,
                                          application.rule(), goal, null, null);
        }

        private Term buildUsageFormula(Goal goal) {
            return services.getTermBuilder().prog(
                instantiation.modality,
                replaceBlock(instantiation.formula.javaBlock(),
                             instantiation.block,
                             constructAbruptTerminationIfCascade()),
                instantiation.formula.sub(0),
                TermLabelManager.instantiateLabels(
                    termLabelState, services, occurrence,
                    application.rule(), application, goal,
                    BlockContractHint.USAGE_BRANCH, null,
                    instantiation.modality,
                    new ImmutableArray<Term>(instantiation.formula.sub(0)),
                    null, instantiation.formula.javaBlock(),
                    instantiation.formula.getLabels())
            );
        }

        private JavaBlock replaceBlock(final JavaBlock java,
                                       final StatementBlock oldBlock,
                                       final StatementBlock newBlock) {
            Statement newProgram =
                (Statement) new ProgramElementReplacer(java.program(), services)
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
                new NotEquals(new ExtList(new Expression[] {variables.exception,
                                                            NullLiteral.NULL})),
                KeYJavaASTFactory.throwClause(variables.exception)));
            return new StatementBlock(ifCascade.toArray(new Statement[ifCascade.size()]));
        }

    }
}
