/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.*;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import de.uka.ilkd.key.informationflow.proof.InfFlowCheckInfo;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.expression.operator.NotEquals;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.java.visitor.OuterBreakContinueAndReturnCollector;
import de.uka.ilkd.key.java.visitor.OuterBreakContinueAndReturnReplacer;
import de.uka.ilkd.key.java.visitor.ProgramElementReplacer;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.macros.WellDefinednessMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.StrategyInfoUndoMethod;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.rule.AbstractAuxiliaryContractRule.Instantiation;
import de.uka.ilkd.key.rule.AbstractBlockContractRule.BlockContractHint;
import de.uka.ilkd.key.rule.metaconstruct.IntroAtPreDefsOp;
import de.uka.ilkd.key.speclang.AuxiliaryContract;
import de.uka.ilkd.key.speclang.AuxiliaryContract.Variables;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.BlockWellDefinedness;
import de.uka.ilkd.key.speclang.LoopContract;
import de.uka.ilkd.key.util.LinkedHashMap;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.util.ExtList;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

/**
 * This contains various builders used in building formulae and terms for block and loop contracts.
 *
 * @author wacker, lanzinger
 */
public final class AuxiliaryContractBuilders {

    /**
     * Prefix for all anonymization constants in {@link UpdatesBuilder#buildAnonInUpdate(Map)}.
     */
    public static final String ANON_IN_PREFIX = "anonIn_";

    /**
     * Prefix for all anonymization constants in
     * {@link UpdatesBuilder#buildAnonOutUpdate(Map, Map)}.
     */
    public static final String ANON_OUT_PREFIX = "anonOut_";

    private AuxiliaryContractBuilders() {
    }

    /**
     * This class is used to construct {@code block'} from {@code block} (see Wacker 2012, 3.3).
     *
     * @see ValidityProgramConstructor#construct()
     */
    public static final class ValidityProgramConstructor {

        /**
         * @see AuxiliaryContract#getLabels()
         */
        private final Iterable<Label> labels;

        /**
         * @see AuxiliaryContract#getBlock()
         */
        private final StatementBlock block;

        /**
         * @see AuxiliaryContract#getVariables()
         */
        private final BlockContract.Variables variables;

        /**
         * The subset of variables that have already been declared.
         */
        private final BlockContract.Variables alreadyDeclared;

        /**
         * Services.
         */
        private final Services services;

        /**
         * Statements in the program.
         */
        private final List<Statement> statements;

        /**
         * The exception variable.
         */
        private final ProgramVariable exceptionParameter;

        /**
         *
         * @param labels all labels belonging to the block.
         * @param block the block.
         * @param variables the variables.
         * @param exceptionParameter the exception variable.
         * @param services services.
         */
        public ValidityProgramConstructor(final Iterable<Label> labels, final StatementBlock block,
                final BlockContract.Variables variables, final ProgramVariable exceptionParameter,
                final Services services) {
            this(labels, block, variables, exceptionParameter, services, null);
        }

        /**
         *
         * @param labels all labels belonging to the block.
         * @param block the block.
         * @param variables the variables.
         * @param exceptionParameter the exception variable.
         * @param services services.
         * @param alreadyDeclared the subset of variables that have already been declared.
         */
        public ValidityProgramConstructor(final Iterable<Label> labels, final StatementBlock block,
                final BlockContract.Variables variables, final ProgramVariable exceptionParameter,
                final Services services, final BlockContract.Variables alreadyDeclared) {
            this.labels = labels;
            this.block = block;
            this.variables = variables;
            this.services = services;
            this.exceptionParameter = exceptionParameter;
            statements = new LinkedList<>();
            this.alreadyDeclared = alreadyDeclared;
        }

        /**
         *
         * @return block'
         */
        public StatementBlock construct() {
            declareFlagsFalse();
            declareResultDefault();
            declareExceptionNull();
            executeBlockSafely();
            return new StatementBlock(statements.toArray(new Statement[0]));
        }

        /**
         * Adds statements to declare all flags that have not yet been declared and set their values
         * to false.
         */
        private void declareFlagsFalse() {
            for (ProgramVariable flag : variables.breakFlags.values()) {
                if (alreadyDeclared != null && alreadyDeclared.breakFlags.containsValue(flag)) {
                    statements.add(KeYJavaASTFactory.assign(flag, BooleanLiteral.FALSE));
                } else {
                    statements.add(KeYJavaASTFactory.declare(flag, BooleanLiteral.FALSE,
                        services.getJavaInfo().getKeYJavaType("boolean")));
                }
            }

            for (ProgramVariable flag : variables.continueFlags.values()) {
                if (alreadyDeclared != null && alreadyDeclared.continueFlags.containsValue(flag)) {
                    statements.add(KeYJavaASTFactory.assign(flag, BooleanLiteral.FALSE));
                } else {
                    statements.add(KeYJavaASTFactory.declare(flag, BooleanLiteral.FALSE,
                        services.getJavaInfo().getKeYJavaType("boolean")));
                }
            }
            if (variables.returnFlag != null) {
                if (alreadyDeclared != null && alreadyDeclared.returnFlag != null) {
                    statements.add(
                        KeYJavaASTFactory.assign(variables.returnFlag, BooleanLiteral.FALSE));
                } else {
                    statements.add(KeYJavaASTFactory.declare(variables.returnFlag,
                        BooleanLiteral.FALSE, services.getJavaInfo().getKeYJavaType("boolean")));
                }
            }
        }

        /**
         * Adds a statement that declares the result variable if necessary and set its value to the
         * default for its type.
         */
        private void declareResultDefault() {
            if (occursReturnAndIsReturnTypeNotVoid()) {
                if (alreadyDeclared != null && alreadyDeclared.result != null) {
                    KeYJavaType resultType = variables.result.getKeYJavaType();
                    statements.add(
                        KeYJavaASTFactory.assign(variables.result, resultType.getDefaultValue()));
                } else {
                    KeYJavaType resultType = variables.result.getKeYJavaType();
                    statements.add(KeYJavaASTFactory.declare(variables.result,
                        resultType.getDefaultValue(), resultType));
                }
            }
        }

        /**
         *
         * @return {@code true} iff there is a result.
         */
        private boolean occursReturnAndIsReturnTypeNotVoid() {
            return variables.returnFlag != null && variables.result != null;
        }

        /**
         * Adds a statement that declares the exception variable if necessary and set its value to
         * {@code null}.
         */
        private void declareExceptionNull() {
            if (alreadyDeclared != null && alreadyDeclared.exception != null) {
                statements.add(KeYJavaASTFactory.assign(variables.exception, NullLiteral.NULL));
            } else {
                statements.add(KeYJavaASTFactory.declare(variables.exception, NullLiteral.NULL,
                    variables.exception.getKeYJavaType()));
            }
        }

        /**
         * Makes sure that the block never terminates abruptly.
         */
        private void executeBlockSafely() {
            final Label breakOutLabel = new ProgramElementName("breakOut");
            final StatementBlock almostSafeBlock =
                replaceOuterBreaksContinuesAndReturns(block, breakOutLabel);
            final Statement labeledAlmostSafeBlock = label(almostSafeBlock, labels);
            final Statement safeStatement =
                wrapInTryCatch(labeledAlmostSafeBlock, exceptionParameter);
            statements.add(
                new LabeledStatement(breakOutLabel, safeStatement, PositionInfo.UNDEFINED));
        }

        /**
         *
         * @param block a block.
         * @param labels labels that should be added to the block.
         * @return a labeled statement.
         */
        private Statement label(final StatementBlock block, Iterable<Label> labels) {
            Statement result = block;
            for (Label label : labels) {
                result = new LabeledStatement(label, result, PositionInfo.UNDEFINED);
            }
            return result;
        }

        /**
         *
         * @param block a block.
         * @param breakOutLabel a label belonging to the block.
         * @return the block with all outer breaks, continues, and returns replaced.
         * @see OuterBreakContinueAndReturnReplacer
         */
        private StatementBlock replaceOuterBreaksContinuesAndReturns(final StatementBlock block,
                final Label breakOutLabel) {
            return new OuterBreakContinueAndReturnReplacer(block, labels, breakOutLabel,
                variables.breakFlags, variables.continueFlags, variables.returnFlag,
                variables.result, variables.exception, services).replace();
        }

        /**
         *
         * @param labeledBlock the labeled block.
         * @param exceptionParameter the exception variable.
         * @return wraps the labeled block in a try-catch structure
         */
        private Statement wrapInTryCatch(final Statement labeledBlock,
                final ProgramVariable exceptionParameter) {
            Catch katch = KeYJavaASTFactory.catchClause(
                KeYJavaASTFactory.parameterDeclaration(services.getJavaInfo(),
                    exceptionParameter.getKeYJavaType(), exceptionParameter),
                new StatementBlock(
                    KeYJavaASTFactory.assign(variables.exception, exceptionParameter)));
            return new Try(new StatementBlock(labeledBlock), new Branch[] { katch });
        }
    }

    /**
     * This class contains methods to create new variables from the contract's placeholder variables
     * (see {@link BlockContract#getPlaceholderVariables()}), and register them.
     */
    public static final class VariablesCreatorAndRegistrar {

        /**
         * The current goal.
         */
        private final Goal goal;

        /**
         * @see AuxiliaryContract#getPlaceholderVariables()
         */
        private final BlockContract.Variables placeholderVariables;

        /**
         * Services.
         */
        private final Services services;

        /**
         *
         * @param goal If this is not null, all created variables are added to it. If it is null,
         *        the variables are instead added to the {@code services}' namespace.
         * @param placeholderVariables the placeholders from which to create the variables.
         * @param services services.
         */
        public VariablesCreatorAndRegistrar(final Goal goal,
                final BlockContract.Variables placeholderVariables, final Services services) {
            this.goal = goal;
            this.placeholderVariables = placeholderVariables;
            this.services = services;
        }

        /**
         *
         * @param self the self term
         * @param existingPO {@code true} if we are applying a rule in an existing proof obligation,
         *        {@code false} if we are creating a new proof obligation.
         * @return the registered variables.
         */
        public Variables createAndRegister(Term self, boolean existingPO) {
            return createAndRegister(self, existingPO, null);
        }

        /**
         *
         * @param self the self term
         * @param existingPO {@code true} if we are applying a rule in an existing proof obligation,
         *        {@code false} if we are creating a new proof obligation.
         * @param pe if {@code existingPO == false}, all contracts on blocks in this program element
         *        will have their remembrance variables replaced by the one created here.
         * @return the registered variables.
         */
        public Variables createAndRegister(Term self, boolean existingPO, ProgramElement pe) {
            if (existingPO) {
                // In an existing PO, the outer remembrance vars already exist and refer to the
                // current method's prestate.
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
                    placeholderVariables.outerRemembranceHeaps,
                    placeholderVariables.outerRemembranceVariables, services);
            } else {
                // In a new PO, the outer remembrance vars don't exist yet.
                Map<LocationVariable, LocationVariable> outerRemembranceHeaps =
                    createAndRegisterRemembranceVariables(
                        placeholderVariables.outerRemembranceHeaps);
                Map<LocationVariable, LocationVariable> outerRemembranceVariables =
                    createAndRegisterRemembranceVariables(
                        placeholderVariables.outerRemembranceVariables);

                replaceOuterRemembranceVarsInInnerContracts(pe, outerRemembranceHeaps,
                    outerRemembranceVariables);

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
                    outerRemembranceHeaps, outerRemembranceVariables, services);
            }
        }

        /**
         * Creates and registers copies of the remembrance variables and heaps.
         *
         * @param suffix a suffix for the new variables' names.
         * @return a {@link Variables} object containing the new {@link ProgramVariables}.
         */
        public Variables createAndRegisterCopies(String suffix) {
            return new BlockContract.Variables(null, placeholderVariables.breakFlags,
                placeholderVariables.continueFlags, placeholderVariables.returnFlag,
                placeholderVariables.result, placeholderVariables.exception,
                createAndRegisterRemembranceVariables(
                    appendSuffix(placeholderVariables.remembranceHeaps, suffix)),
                createAndRegisterRemembranceVariables(
                    appendSuffix(placeholderVariables.remembranceLocalVariables, suffix)),
                placeholderVariables.outerRemembranceHeaps,
                placeholderVariables.outerRemembranceVariables, services);
        }

        /**
         *
         * @param map a map containing variables.
         * @param suffix a suffix.
         * @return the map with the suffix appended to every variable's name.
         */
        private <K> Map<K, LocationVariable> appendSuffix(final Map<K, LocationVariable> map,
                final String suffix) {
            final Map<K, LocationVariable> result = new LinkedHashMap<>();

            for (Entry<K, LocationVariable> entry : map.entrySet()) {
                K key = entry.getKey();
                LocationVariable value = entry.getValue();

                String newName =
                    services.getTermBuilder().newName(value.name().toString() + suffix);
                LocationVariable newValue =
                    new LocationVariable(new ProgramElementName(newName), value.getKeYJavaType());

                result.put(key, newValue);
            }

            return result;
        }

        /**
         *
         * @param placeholderFlags the placeholder flags.
         * @return newly created and registered flags with the same names.
         */
        private Map<Label, ProgramVariable> createAndRegisterFlags(
                final Map<Label, ProgramVariable> placeholderFlags) {
            Map<Label, ProgramVariable> result = new LinkedHashMap<>();
            for (Map.Entry<Label, ProgramVariable> flag : placeholderFlags.entrySet()) {
                result.put(flag.getKey(), createAndRegisterVariable(flag.getValue()));
            }
            return result;
        }

        /**
         *
         * @param remembranceVariables the placeholder remembrance variables.
         * @return newly created and registered remembrance variables with the same names.
         */
        private Map<LocationVariable, LocationVariable> createAndRegisterRemembranceVariables(
                final Map<LocationVariable, LocationVariable> remembranceVariables) {
            final Map<LocationVariable, LocationVariable> result =
                new LinkedHashMap<>();
            for (Map.Entry<LocationVariable, LocationVariable> remembranceVariable : remembranceVariables
                    .entrySet()) {
                result.put(remembranceVariable.getKey(),
                    createAndRegisterVariable(remembranceVariable.getValue()));
            }
            return result;
        }

        /**
         *
         * @param placeholderVariable a placeholder variable
         * @return a newly created and registered variable with the same name.
         */
        private LocationVariable createAndRegisterVariable(
                final ProgramVariable placeholderVariable) {
            if (placeholderVariable != null) {
                String newName =
                    services.getTermBuilder().newName(placeholderVariable.name().toString());
                LocationVariable newVariable = new LocationVariable(new ProgramElementName(newName),
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

        /**
         * Replace the outer remembrance variables of all contracts on blocks in {@code pe}.
         *
         * @param pe the program elements.
         * @param outerRemembranceHeaps the new outer remembrance heaps.
         * @param outerRemembranceVariables the new outer remembrance variables.
         * @see #createAndRegister(Term, boolean, ProgramElement)
         */
        private void replaceOuterRemembranceVarsInInnerContracts(ProgramElement pe,
                Map<LocationVariable, LocationVariable> outerRemembranceHeaps,
                Map<LocationVariable, LocationVariable> outerRemembranceVariables) {
            ImmutableSet<JavaStatement> innerBlocksAndLoops = new JavaASTVisitor(pe, services) {
                private ImmutableSet<JavaStatement> statements = DefaultImmutableSet.nil();

                @Override
                protected void doDefaultAction(SourceElement node) {
                    if (node instanceof StatementBlock || node instanceof LoopStatement) {
                        statements = statements.add((JavaStatement) node);
                    }
                }

                public ImmutableSet<JavaStatement> run() {
                    walk(root());
                    return statements;
                }
            }.run();

            IntroAtPreDefsOp transformer =
                (IntroAtPreDefsOp) AbstractTermTransformer.INTRODUCE_ATPRE_DEFINITIONS;
            final Map<LocationVariable, LocationVariable> atPreVars =
                new LinkedHashMap<>();
            atPreVars.putAll(outerRemembranceHeaps);
            atPreVars.putAll(outerRemembranceVariables);
            transformer.updateBlockAndLoopContracts(innerBlocksAndLoops, atPreVars,
                outerRemembranceHeaps, services);
        }
    }

    /**
     * This class is used to build the various updates that are needed for block/loop contract
     * rules.
     */
    public static final class UpdatesBuilder extends TermBuilder {

        /**
         * @see AuxiliaryContract#getVariables()
         */
        private final BlockContract.Variables variables;

        /**
         *
         * @param variables the variables for the contract being applied.
         * @param services services.
         */
        public UpdatesBuilder(final BlockContract.Variables variables, final Services services) {
            super(services.getTermFactory(), services);
            this.variables = variables;
        }

        /**
         *
         * @param heaps the heaps.
         * @return a remembrance update for the specified heaps.
         */
        public Term buildRemembranceUpdate(final List<LocationVariable> heaps) {
            Term result = skip();
            for (LocationVariable heap : heaps) {
                final Term update = elementary(variables.remembranceHeaps.get(heap), var(heap));
                result = parallel(result, update);
            }
            for (Map.Entry<LocationVariable, LocationVariable> remembranceVariable : variables.remembranceLocalVariables
                    .entrySet()) {
                result = parallel(result,
                    elementary(remembranceVariable.getValue(), var(remembranceVariable.getKey())));
            }
            return result;
        }

        /**
         *
         * @return an outer remembrance update.
         */
        public Term buildOuterRemembranceUpdate() {
            Term result = skip();

            for (LocationVariable var : variables.outerRemembranceHeaps.keySet()) {
                final Term update = elementary(variables.outerRemembranceHeaps.get(var), var(var));
                result = parallel(result, update);
            }

            for (LocationVariable var : variables.outerRemembranceVariables.keySet()) {
                final Term update =
                    elementary(variables.outerRemembranceVariables.get(var), var(var));
                result = parallel(result, update);
            }

            return result;
        }

        /**
         *
         * @param anonymisationHeaps anonymization heaps.
         * @param modifiesClauses modifies clauses for the specified heaps.
         * @return an anonymization update for the specified modifies clauses.
         */
        public Term buildAnonOutUpdate(final Map<LocationVariable, Function> anonymisationHeaps,
                final Map<LocationVariable, Term> modifiesClauses) {
            return buildAnonOutUpdate(variables.remembranceLocalVariables.keySet(),
                anonymisationHeaps, modifiesClauses, ANON_OUT_PREFIX);
        }

        /**
         *
         * @param el a program element
         * @param anonymisationHeaps anonymization heaps.
         * @param modifiesClauses modifies clauses for the specified heaps.
         * @return an anonymization update for the specified modifies clauses and for every modified
         *         variable that occurs in the specified program element.
         */
        public Term buildAnonOutUpdate(final ProgramElement el,
                final Map<LocationVariable, Function> anonymisationHeaps,
                final Map<LocationVariable, Term> modifiesClauses) {
            return buildAnonOutUpdate(el, anonymisationHeaps, modifiesClauses, ANON_OUT_PREFIX);
        }

        /**
         *
         * @param el a program element
         * @param anonymisationHeaps anonymization heaps.
         * @param modifiesClauses modifies clauses for the specified heaps.
         * @param prefix a prefix for the name of the anon functions.
         * @return an anonymization update for the specified modifies clauses and for every modified
         *         variable that occurs in the specified program element.
         */
        public Term buildAnonOutUpdate(final ProgramElement el,
                final Map<LocationVariable, Function> anonymisationHeaps,
                final Map<LocationVariable, Term> modifiesClauses, final String prefix) {
            return buildAnonOutUpdate(
                MiscTools.getLocalOuts(el, services).stream()
                        .filter(LocationVariable.class::isInstance)
                        .map(LocationVariable.class::cast).collect(Collectors.toSet()),
                anonymisationHeaps, modifiesClauses, prefix);
        }

        /**
         *
         * @param vars a set of variables
         * @param anonymisationHeaps anonymization heaps.
         * @param modifiesClauses modifies clauses for the specified heaps.
         * @param prefix a prefix for the name of the anon functions.
         * @return an anonymization update for the specified modifies clauses and for every variable
         *         in the specified set.
         */
        public Term buildAnonOutUpdate(final Set<LocationVariable> vars,
                final Map<LocationVariable, Function> anonymisationHeaps,
                final Map<LocationVariable, Term> modifiesClauses, final String prefix) {
            Term result = buildLocalVariablesAnonUpdate(vars, prefix);
            for (Map.Entry<LocationVariable, Function> anonymisationHeap : anonymisationHeaps
                    .entrySet()) {
                Term anonymisationUpdate = skip();
                final Term modifiesClause = modifiesClauses.get(anonymisationHeap.getKey());
                if (!modifiesClause.equalsModIrrelevantTermLabels(strictlyNothing())) {
                    anonymisationUpdate = anonUpd(anonymisationHeap.getKey(), modifiesClause,
                        services.getTermBuilder().label(
                            services.getTermBuilder().func(anonymisationHeap.getValue()),
                            ParameterlessTermLabel.ANON_HEAP_LABEL));
                }
                result = parallel(result, anonymisationUpdate);
            }
            return result;
        }

        /**
         *
         * @param anonymisationHeaps anonymization heaps.
         * @return an anonymization update for all heap locations.
         */
        public Term buildAnonInUpdate(final Map<LocationVariable, Function> anonymisationHeaps) {
            Term result = buildLocalVariablesAnonUpdate(
                variables.outerRemembranceVariables.keySet(), ANON_IN_PREFIX);

            for (Map.Entry<LocationVariable, Function> anonymisationHeap : anonymisationHeaps
                    .entrySet()) {
                Term anonymisationUpdate = skip();

                anonymisationUpdate = anonUpd(anonymisationHeap.getKey(), allLocs(),
                    services.getTermBuilder().label(
                        services.getTermBuilder().func(anonymisationHeap.getValue()),
                        ParameterlessTermLabel.ANON_HEAP_LABEL));

                result = parallel(result, anonymisationUpdate);
            }

            return result;
        }

        /**
         *
         * @param vars a collection of variables.
         * @param prefix a prefix for the name of the anonymization constants.
         * @return an anonymization update for the specified variables.
         */
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

    /**
     * This class is used to build various sub-formulas used in the block/loop contract rules.s
     */
    public static final class ConditionsAndClausesBuilder extends TermBuilder {

        /**
         * @see AuxiliaryContract#getVariables()
         * @see AuxiliaryContract.Variables#termify(Term)
         */
        final BlockContract.Terms terms;

        /**
         * The contract being applied
         */
        private final AuxiliaryContract contract;

        /**
         * The heaps.
         */
        private final List<LocationVariable> heaps;

        /**
         * @see AuxiliaryContract#getVariables()
         */
        private final BlockContract.Variables variables;

        /**
         *
         * @param contract the contract being applied.
         * @param heaps the heaps.
         * @param variables the variables.
         * @param self the self term.
         * @param services services.
         */
        public ConditionsAndClausesBuilder(final AuxiliaryContract contract,
                final List<LocationVariable> heaps, final BlockContract.Variables variables,
                final Term self, final Services services) {
            super(services.getTermFactory(), services);
            this.contract = contract;
            this.heaps = heaps;
            this.variables = variables;
            this.terms = variables.termify(self);
        }

        /**
         *
         * @return the termified variables.
         */
        public AuxiliaryContract.Terms getTerms() {
            return terms;
        }

        /**
         *
         * @return the contract's precondition.
         */
        public Term buildPrecondition() {
            Term result = tt();

            for (LocationVariable heap : heaps) {
                result =
                    and(result, contract.getPrecondition(heap, getBaseHeap(), terms, services));
            }

            return result;
        }

        /**
         *
         * @return the contract's free precondition.
         */
        public Term buildFreePrecondition() {
            Term result = tt();

            for (LocationVariable heap : heaps) {
                result =
                    and(result, contract.getFreePrecondition(heap, getBaseHeap(), terms, services));
            }

            return result;
        }

        /**
         *
         * @return the condition that all heaps are well-formed.
         */
        public Term buildWellFormedHeapsCondition() {
            Term result = tt();
            for (LocationVariable heap : heaps) {
                result = and(result, wellFormed(heap));
            }
            return result;
        }

        /**
         *
         * @param localInVariables all free local variables in the block.
         * @return the condition that all of those variables have valid values.
         */
        public Term buildReachableInCondition(
                final ImmutableSet<ProgramVariable> localInVariables) {
            return buildReachableCondition(localInVariables);
        }

        /**
         *
         * @param localOutVariables all free local variables modified by the block.
         * @return the condition that all of those variables have valid values.
         */
        public Term buildReachableOutCondition(
                final ImmutableSet<ProgramVariable> localOutVariables) {
            final Term reachableResult =
                (variables.result != null) ? reachableValue(variables.result)
                        : services.getTermBuilder().tt();
            return and(buildReachableCondition(localOutVariables), reachableResult,
                reachableValue(variables.exception));
        }

        /**
         *
         * @param variables a set of variables.
         * @return the condition that all of those variables have valid values.
         */
        public Term buildReachableCondition(final ImmutableSet<ProgramVariable> variables) {
            Term result = tt();
            for (ProgramVariable variable : variables) {
                result = and(result, reachableValue(variable));
            }
            return result;
        }

        /**
         *
         * @return the contract's modifies clauses.
         */
        public Map<LocationVariable, Term> buildModifiesClauses() {
            Map<LocationVariable, Term> result = new LinkedHashMap<>();
            for (final LocationVariable heap : heaps) {
                result.put(heap, contract.getModifiesClause(heap, var(heap), terms.self, services));
            }
            return result;
        }

        /**
         *
         * @return the contract's free modifies clauses.
         */
        public Map<LocationVariable, Term> buildFreeModifiesClauses() {
            Map<LocationVariable, Term> result = new LinkedHashMap<>();
            for (final LocationVariable heap : heaps) {
                result.put(heap,
                    contract.getFreeModifiesClause(heap, var(heap), terms.self, services));
            }
            return result;
        }

        /**
         *
         * @return the loop contract's decreases clause.
         */
        public Term buildDecreasesCheck() {
            if (!(contract instanceof LoopContract)) {
                throw new IllegalStateException();
            }

            LoopContract lc = (LoopContract) contract;
            Term decreases = lc.getDecreases(getBaseHeap(), terms.self, services);

            if (decreases == null) {
                return tt();
            }

            Term oldDecreases = new OpReplacer(variables.combineRemembranceVariables(),
                services.getTermFactory(), services.getProof()).replace(decreases);

            // The condition (decreases >= 0) is part of the precondition
            // and does not need to be repeated here.
            return lt(decreases, oldDecreases);
        }

        /**
         *
         * @return the contract's postcondition.
         */
        public Term buildPostcondition() {
            Term result = tt();
            for (LocationVariable heap : heaps) {
                result =
                    and(result, contract.getPostcondition(heap, getBaseHeap(), terms, services));
            }
            return result;
        }

        /**
         *
         * @return the contract's postcondition.
         */
        public Term buildFreePostcondition() {
            Term result = tt();
            for (LocationVariable heap : heaps) {
                result = and(result,
                    contract.getFreePostcondition(heap, getBaseHeap(), terms, services));
            }
            return result;
        }

        /**
         *
         * @param modifiesClauses the contract's modifies clauses
         * @param freeModifiesClauses the contract's free modifies clauses
         * @return the contract's framing condition.
         */
        public Term buildFrameCondition(
                final Map<LocationVariable, Term> modifiesClauses,
                final Map<LocationVariable, Term> freeModifiesClauses) {
            Term result = tt();
            Map<LocationVariable, Map<Term, Term>> remembranceVariables =
                constructRemembranceVariables();
            for (LocationVariable heap : heaps) {
                final Term modifiesClause = modifiesClauses.get(heap);
                final Term freeModifiesClause = freeModifiesClauses.get(heap);
                final Term frameCondition;
                if (!contract.hasModifiesClause(heap)) {
                    if (!contract.hasFreeModifiesClause(heap)) {
                        frameCondition = frameStrictlyEmpty(
                            var(heap), remembranceVariables.get(heap));
                    } else {
                        frameCondition =
                            frame(var(heap), remembranceVariables.get(heap), freeModifiesClause);
                    }
                } else {
                    if (!contract.hasFreeModifiesClause(heap)) {
                        frameCondition = frame(
                            var(heap), remembranceVariables.get(heap), modifiesClause);
                    } else {
                        frameCondition = frame(var(heap), remembranceVariables.get(heap),
                            union(modifiesClause, freeModifiesClause));
                    }
                }
                result = and(result, frameCondition);
            }
            return result;
        }

        /**
         *
         * @return a map from every variable to its remembrance variable, for every heap.
         */
        private Map<LocationVariable, Map<Term, Term>> constructRemembranceVariables() {
            Map<LocationVariable, Map<Term, Term>> result =
                new LinkedHashMap<>();
            for (Map.Entry<LocationVariable, LocationVariable> remembranceHeap : variables.remembranceHeaps
                    .entrySet()) {
                final LocationVariable heap = remembranceHeap.getKey();
                result.put(heap, new LinkedHashMap<>());
                result.get(heap).put(var(heap), var(remembranceHeap.getValue()));
            }
            for (Map.Entry<LocationVariable, LocationVariable> remembranceLocalVariable : variables.remembranceLocalVariables
                    .entrySet()) {
                result.get(getBaseHeapFunction()).put(var(remembranceLocalVariable.getKey()),
                    var(remembranceLocalVariable.getValue()));
            }
            return result;
        }

        /**
         *
         * @return the base heap.
         */
        private LocationVariable getBaseHeapFunction() {
            return services.getTypeConverter().getHeapLDT().getHeap();
        }

        /**
         *
         * @param anonymisationHeaps anonymisation heaps.
         * @return the condition that all anonymisation heaps are well-formed.
         */
        public Term buildWellFormedAnonymisationHeapsCondition(
                final Map<LocationVariable, Function> anonymisationHeaps) {
            Term result = tt();
            for (Function anonymisationFunction : anonymisationHeaps.values()) {
                result = and(result,
                    wellFormed(services.getTermBuilder().label(
                        services.getTermBuilder().func(anonymisationFunction),
                        ParameterlessTermLabel.ANON_HEAP_LABEL)));
            }
            return result;
        }

        /**
         *
         * @return the condition that at most one flag for abrupt termination is {@code true}.
         */
        public Term buildAtMostOneFlagSetCondition() {
            final List<Term> notSetConditions = new LinkedList<>();
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
         * @param heaps the heaps.
         * @param pm the method containg the block.
         * @param selfKJT the self variable's type.
         * @param self the self variable.
         * @param services services.
         * @return the assumptions for the {@code self} variable.
         */
        public Term buildSelfConditions(List<LocationVariable> heaps, IProgramMethod pm,
                KeYJavaType selfKJT, Term self, Services services) {
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

                return and(notNull, created, exactType);
            } else {
                return tt();
            }
        }

        /**
         *
         * @param flags a collection of boolean variables.
         * @return the condition that all flags are {@code false}.
         */
        private List<Term> buildFlagsNotSetConditions(final Collection<ProgramVariable> flags) {
            final List<Term> result = new LinkedList<>();
            for (ProgramVariable flag : flags) {
                result.add(buildFlagNotSetCondition(flag));
            }
            return result;
        }

        /**
         *
         * @param flag a boolean variable.
         * @return the condition that the flag is {@code false}.
         */
        private Term buildFlagNotSetCondition(final ProgramVariable flag) {
            return equals(var(flag), FALSE());
        }
    }

    /**
     * This class contains methods to add the premisses for the block contract rule to the goal.
     */
    public final static class GoalsConfigurator {

        /**
         * The rule application.
         */
        private final AbstractAuxiliaryContractBuiltInRuleApp application;

        /**
         * The term label state.
         */
        private final TermLabelState termLabelState;

        /**
         * The instantiation.
         */
        private final Instantiation instantiation;

        /**
         * @see AuxiliaryContract#getLabels()
         */
        private final List<Label> labels;

        /**
         * @see AuxiliaryContract#getVariables()
         */
        private final AuxiliaryContract.Variables variables;

        /**
         * The position at which the rule is applied.
         */
        private final PosInOccurrence occurrence;

        /**
         * Services.
         */
        private final Services services;

        /**
         * The rule being applied.
         */
        private final AbstractAuxiliaryContractRule rule;

        /**
         *
         * @param application the rule application.
         * @param termLabelState the term label state.
         * @param instantiation the instantiation
         * @param labels all labels belonging to the block.
         * @param variables the contract's variables.
         * @param occurrence the position at which the rule is applied.
         * @param services services.
         * @param rule the rule being applied.
         */
        public GoalsConfigurator(final AbstractAuxiliaryContractBuiltInRuleApp application,
                final TermLabelState termLabelState, final Instantiation instantiation,
                final List<Label> labels, final AuxiliaryContract.Variables variables,
                final PosInOccurrence occurrence, final Services services,
                final AbstractAuxiliaryContractRule rule) {
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
         * Adds information flow properties to the specified goal.
         *
         * @param goal a goal.
         */
        private static void addInfFlow(final Goal goal) {
            final boolean oldInfFlowCheckInfoValue =
                goal.getStrategyInfo(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY) != null
                        && goal.getStrategyInfo(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY);
            StrategyInfoUndoMethod undo =
                strategyInfos -> strategyInfos.put(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY,
                    oldInfFlowCheckInfoValue);
            goal.addStrategyInfo(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY, false, undo);
        }

        /**
         *
         * @param services services.
         * @return additional program variables necessary for loop contract rules.
         */
        private static ProgramVariable[] createLoopVariables(final Services services) {
            ProgramVariable conditionVariable = AbstractAuxiliaryContractRule.createLocalVariable(
                "cond", services.getJavaInfo().getKeYJavaType("boolean"), services);

            ProgramVariable brokeLoopVariable = AbstractAuxiliaryContractRule.createLocalVariable(
                "brokeLoop", services.getJavaInfo().getKeYJavaType("boolean"), services);

            ProgramVariable continuedLoopVariable =
                AbstractAuxiliaryContractRule.createLocalVariable("continuedLoop",
                    services.getJavaInfo().getKeYJavaType("boolean"), services);
            final ProgramVariable[] loopVariables = new ProgramVariable[] { conditionVariable,
                brokeLoopVariable, continuedLoopVariable };
            return loopVariables;
        }

        /**
         *
         * @param goal the current goal
         * @param contract a loop contract.
         * @param unfold the evaluation of the loop guard.
         * @param body the loop body.
         * @param tail all statements in the block after the loop.
         * @param modality the contract's modality.
         * @param bodyBreakFound whether or not the body contains a break statement.
         * @param context the context update.
         * @param remember the remembrance update.
         * @param rememberNext the remembracne update for the next loop iteration.
         * @param decreasesCheck the decreases check.
         * @param anonOut the anonOut update.
         * @param anonOut2 a copy of the anonOut update.
         * @param post the current loop iteration's postconditon.
         * @param postNext the next loop iteration's postconditon.
         * @param postAfterTail the formula {@code [[tail]] -> post} where {@code [[]]} the
         *        contract's modality.
         * @param pre the contract's precondition.
         * @param brokeLoop the formula {@code brokeLoop = true}
         * @param notBrokeLoop the formula {@code not brokeLoop = true}
         * @param exceptionEqNull the formula {@code exception = null}
         * @param exceptionNeqNull the formula {@code not exception = null}
         * @param cond the formula {@code cond = true}
         * @param notCond the formula {@code not cond = true}
         * @param abrupt the formula for abrupt termination.
         * @param notAbrupt the negation of the formula for abrupt termination.
         * @param tb a term builder.
         * @return the sequent for the validity branch in a loop contract rule.
         */
        private static Term buildLoopValiditySequent(final Goal goal, final LoopContract contract,
                JavaBlock unfold, JavaBlock body, JavaBlock tail, final Modality modality,
                boolean bodyBreakFound, final Term context, final Term remember,
                final Term rememberNext, final Term decreasesCheck, Term anonOut, Term anonOut2,
                Term post, Term postNext, Term postAfterTail, Term pre, Term brokeLoop,
                Term notBrokeLoop, Term exceptionEqNull, Term exceptionNeqNull, Term cond,
                Term notCond, Term abrupt, Term notAbrupt, final TermBuilder tb) {
            Term update;
            if (goal == null) {
                // We are building a proof obligation for a loop contract.
                // Thus, the "context" update already anonymizes all variables.
                update = context;
            } else {
                // We are building the validity branch for an application of
                // LoopContractInternalRule.
                // Thus, the "context" update contains the surrounding methods context, and we need
                // to anonymize all variables modified by the loop body.
                update = tb.sequential(context, anonOut2);
            }

            Term term;
            if (contract.getTail().isEmpty()) {
                Term postBody =
                    buildSimplifiedPostBody(bodyBreakFound, rememberNext, decreasesCheck, anonOut,
                        post, postNext, pre, brokeLoop, notBrokeLoop, abrupt, notAbrupt, tb);

                term = tb.apply(update,
                    tb.imp(pre,
                        tb.apply(remember,
                            tb.prog(modality, unfold,
                                tb.and(tb.imp(tb.or(exceptionNeqNull, notCond), post),
                                    tb.imp(tb.and(exceptionEqNull, cond),
                                        tb.prog(modality, body, postBody)))))));
            } else {
                Term postBody = buildFullPostBody(bodyBreakFound, tail, modality, rememberNext,
                    decreasesCheck, anonOut, post, postNext, postAfterTail, pre, brokeLoop,
                    notBrokeLoop, abrupt, notAbrupt, tb);

                term = tb.apply(update, tb.imp(pre, tb.apply(remember, tb.prog(modality, unfold,
                    tb.and(tb.imp(exceptionNeqNull, post),
                        tb.imp(tb.and(exceptionEqNull, notCond), postAfterTail), tb.imp(
                            tb.and(exceptionEqNull, cond), tb.prog(modality, body, postBody)))))));
            }
            return term;
        }

        private static Term buildSimplifiedPostBody(boolean bodyBreakFound, final Term rememberNext,
                final Term decreasesCheck, Term anonOut, Term post, Term postNext, Term pre,
                Term brokeLoop, Term notBrokeLoop, Term abrupt, Term notAbrupt,
                final TermBuilder tb) {
            final Term postBody;
            if (bodyBreakFound) {
                postBody = tb.and(tb.imp(tb.or(brokeLoop, abrupt), post),
                    tb.imp(tb.and(notBrokeLoop, notAbrupt), tb.and(pre, decreasesCheck,
                        tb.apply(rememberNext, tb.apply(anonOut, tb.imp(postNext, post))))));
            } else {
                postBody =
                    tb.and(tb.imp(abrupt, post), tb.imp(notAbrupt, tb.and(pre, decreasesCheck,
                        tb.apply(rememberNext, tb.apply(anonOut, tb.imp(postNext, post))))));
            }
            return postBody;
        }

        private static Term buildFullPostBody(boolean bodyBreakFound, JavaBlock tail,
                final Modality modality, final Term rememberNext, final Term decreasesCheck,
                Term anonOut, Term post, Term postNext, Term postAfterTail, Term pre,
                Term brokeLoop, Term notBrokeLoop, Term abrupt, Term notAbrupt,
                final TermBuilder tb) {
            final Term postBody;
            if (bodyBreakFound) {
                postBody = tb.and(tb.imp(brokeLoop, postAfterTail), tb.imp(abrupt, post), tb.imp(
                    tb.and(notBrokeLoop, notAbrupt),
                    tb.and(pre, decreasesCheck, tb.apply(rememberNext, tb.apply(anonOut, tb.and(
                        tb.imp(abrupt, tb.imp(postNext, post)),
                        tb.imp(notAbrupt, tb.prog(modality, tail, tb.imp(postNext, post)))))))));
            } else {
                postBody = tb.and(tb.imp(abrupt, post), tb.imp(notAbrupt,
                    tb.and(pre, decreasesCheck, tb.apply(rememberNext, tb.apply(anonOut, tb.and(
                        tb.imp(abrupt, tb.imp(postNext, post)),
                        tb.imp(notAbrupt, tb.prog(modality, tail, tb.imp(postNext, post)))))))));
            }
            return postBody;
        }

        private static Term createAbruptTerms(final AuxiliaryContract.Terms terms,
                Term exceptionNeqNull, final TermBuilder tb) {
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
            return tb.or(abruptTerms);
        }

        /**
         *
         * @param goal If this is not {@code null}, the returned formula is added to this goal.
         * @param contract the contract being applied.
         * @param update the update.
         * @param anonUpdate the anonymization update.
         * @param heap the heap.
         * @param anonHeap the anonymization heap.
         * @param localIns all free local variables in the block.
         * @return the well-definedness formula.
         */
        public Term setUpWdGoal(final Goal goal, final BlockContract contract, final Term update,
                final Term anonUpdate, final LocationVariable heap, final Function anonHeap,
                final ImmutableSet<ProgramVariable> localIns) {
            // FIXME: Handling of \old-references needs to be investigated,
            // however only completeness is lost, soundness is guaranteed
            final BlockWellDefinedness bwd =
                new BlockWellDefinedness(contract, variables, localIns, services);
            services.getSpecificationRepository().addWdStatement(bwd);
            final LocationVariable heapAtPre = variables.remembranceHeaps.get(heap);
            final Term anon = anonHeap != null ? services.getTermBuilder().func(anonHeap) : null;
            final SequentFormula wdBlock = bwd.generateSequent(variables.self, variables.exception,
                variables.result, heap, heapAtPre, anon, localIns, update, anonUpdate, services);

            if (goal != null) {
                goal.setBranchLabel(WellDefinednessMacro.WD_BRANCH);
                goal.changeFormula(wdBlock, occurrence);
            }

            return wdBlock.formula();
        }

        /**
         *
         * @param goal If this is not {@code null}, the returned term is added to this goal.
         * @param updates the updates.
         * @param assumptions the preconditions.
         * @param postconditions the postconditions.
         * @param exceptionParameter the exception variable.
         * @param terms the termified variables.
         * @return the term for the validity goal.
         */
        public Term setUpValidityGoal(final Goal goal, final Term[] updates,
                final Term[] assumptions, final Term[] postconditions,
                final ProgramVariable exceptionParameter, final AuxiliaryContract.Terms terms) {
            final TermBuilder tb = services.getTermBuilder();
            JavaBlock newJavaBlock = getJavaBlock(exceptionParameter);
            Term newPost = tb.and(postconditions);
            newPost = AbstractOperationPO.addAdditionalUninterpretedPredicateIfRequired(services,
                newPost, ImmutableSLList.<LocationVariable>nil()
                        .prependReverse(terms.remembranceLocalVariables.keySet()),
                terms.exception);
            if (goal != null) {
                goal.setBranchLabel("Validity");
            }
            newPost = TermLabelManager.refactorTerm(termLabelState, services, null, newPost, rule,
                goal, AbstractAuxiliaryContractRule.NEW_POSTCONDITION_TERM_HINT, null);

            Term term;
            if (goal != null) {
                goal.addFormula(
                    new SequentFormula(tb.applySequential(updates, tb.and(assumptions))), true,
                    false);

                ImmutableArray<TermLabel> labels = TermLabelManager.instantiateLabels(
                    termLabelState, services, occurrence, application.rule(), application, goal,
                    BlockContractHint.createValidityBranchHint(variables.exception), null,
                    instantiation.modality, new ImmutableArray<>(newPost), null, newJavaBlock,
                    instantiation.formula.getLabels());

                term = tb.applySequential(updates,
                    tb.prog(instantiation.modality, newJavaBlock, newPost, labels));

                goal.changeFormula(new SequentFormula(term), occurrence);
                TermLabelManager.refactorGoal(termLabelState, services, occurrence,
                    application.rule(), goal, null, null);
                addInfFlow(goal);
            } else {
                Term pre = tb.and(assumptions);
                Term prog =
                    tb.prog(instantiation.modality, newJavaBlock, newPost, new ImmutableArray<>());
                term = tb.applySequential(updates, tb.imp(pre, prog));
            }

            return term;
        }

        /**
         *
         * @param goal If this is not {@code null}, the returned term is added to this goal.
         * @param contract the contract being applied.
         * @param context the context update.
         * @param remember the remembrance update for the current loop iteration.
         * @param rememberNext the remembrance update for the next loop iteration.
         * @param anonOutHeaps the heaps used in the anonOut update.
         * @param modifiesClauses the modified clauses.
         * @param assumptions the assumptions.
         * @param decreasesCheck the decreases check.
         * @param postconditions the current loop iteration's postconditions.
         * @param postconditionsNext the next loop iteration's postconditions.
         * @param exceptionParameter the exception variable.
         * @param terms the termified variables.
         * @param nextVars the variables for the next loop iteration.
         * @return the term for the validity goal in a loop contract rule app.
         */
        public Term setUpLoopValidityGoal(final Goal goal, final LoopContract contract,
                final Term context, final Term remember, final Term rememberNext,
                final Map<LocationVariable, Function> anonOutHeaps,
                final Map<LocationVariable, Term> modifiesClauses,
                final Map<LocationVariable, Term> freeModifiesClauses,
                final Term[] assumptions,
                final Term decreasesCheck, final Term[] postconditions,
                final Term[] postconditionsNext, final ProgramVariable exceptionParameter,
                final AuxiliaryContract.Terms terms, final AuxiliaryContract.Variables nextVars) {
            final TermBuilder tb = services.getTermBuilder();
            final Modality modality = instantiation.modality;

            final ProgramVariable[] loopVariables = createLoopVariables(services);
            OuterBreakContinueAndReturnCollector collector =
                new OuterBreakContinueAndReturnCollector(contract.getBody(), new LinkedList<>(),
                    services);

            List<Break> bodyBreaks = collector.getBreaks();
            List<Continue> bodyContinues = collector.getContinues();
            collector.collect();

            boolean bodyBreakFound = false;
            Map<Label, ProgramVariable> breakFlags = new LinkedHashMap<>(variables.breakFlags);
            for (Break br : bodyBreaks) {
                Label label = br.getLabel();
                if (label == null || contract.getLoopLabels().contains(label)) {
                    breakFlags.put(label, loopVariables[1]);
                    bodyBreakFound = true;
                }
            }
            Map<Label, ProgramVariable> continueFlags =
                collectContinueFlags(contract, loopVariables[2], bodyContinues);
            final JavaBlock[] javaBlocks = createJavaBlocks(contract, loopVariables[0],
                exceptionParameter, breakFlags, continueFlags);

            Term anonOut = new UpdatesBuilder(variables, services)
                    .buildAnonOutUpdate(contract.getLoop(), anonOutHeaps, modifiesClauses);

            Map<LocationVariable, Function> anonOutHeaps2 = new HashMap<>();
            for (LocationVariable heap : anonOutHeaps.keySet()) {
                final String anonymisationName =
                    tb.newName("init_" + ANON_OUT_PREFIX + heap.name());
                final Function anonymisationFunction =
                    new Function(new Name(anonymisationName), heap.sort(), true);
                services.getNamespaces().functions().addSafely(anonymisationFunction);
                anonOutHeaps2.put(heap, anonymisationFunction);
            }
            Term anonOut2 = new UpdatesBuilder(variables, services).buildAnonOutUpdate(
                contract.getLoop(), anonOutHeaps2, modifiesClauses, "init_" + ANON_OUT_PREFIX);

            final Term[] posts = createPosts(goal, postconditions, postconditionsNext, terms, tb);

            Term postAfterTail = tb.prog(modality, javaBlocks[2], posts[0]);
            Term pre = tb.and(assumptions);
            Term brokeLoop = tb.equals(tb.var(loopVariables[1]), tb.TRUE());
            Term notBrokeLoop = tb.not(brokeLoop);
            Term exceptionEqNull = tb.equals(tb.var(variables.exception), tb.NULL());
            Term exceptionNeqNull = tb.not(exceptionEqNull);
            Term cond = tb.equals(tb.var(loopVariables[0]), tb.TRUE());
            Term notCond = tb.not(cond);
            Term abrupt = createAbruptTerms(terms, exceptionNeqNull, tb);
            Term notAbrupt = tb.not(abrupt);

            final Term term = buildLoopValiditySequent(goal, contract, javaBlocks[0], javaBlocks[1],
                javaBlocks[2], modality, bodyBreakFound, context, remember, rememberNext,
                decreasesCheck, anonOut, anonOut2, posts[0], posts[1], postAfterTail, pre,
                brokeLoop, notBrokeLoop, exceptionEqNull, exceptionNeqNull, cond, notCond, abrupt,
                notAbrupt, tb);
            if (goal != null) {
                goal.setBranchLabel("Validity");
                addInfFlow(goal);
                goal.changeFormula(new SequentFormula(term), occurrence);
            }
            return term;
        }

        /**
         * Sets up the precondition goal.
         *
         * @param goal the precondition goal.
         * @param update the update.
         * @param preconditions the preconditions.
         */
        public void setUpPreconditionGoal(final Goal goal, final Term update,
                final Term[] preconditions) {
            final TermBuilder tb = services.getTermBuilder();
            goal.setBranchLabel("Precondition");
            Term fullPrecondition = tb.apply(update, tb.and(preconditions), null);
            fullPrecondition =
                TermLabelManager.refactorTerm(termLabelState, services, null, fullPrecondition,
                    rule, goal, BlockContractInternalRule.FULL_PRECONDITION_TERM_HINT, null);
            goal.changeFormula(new SequentFormula(fullPrecondition), occurrence);
            TermLabelManager.refactorGoal(termLabelState, services, occurrence, application.rule(),
                goal, null, null);
        }

        /**
         * Sets up the usage goal.
         *
         * @param goal the usage goal.
         * @param updates the updates.
         * @param assumptions the preconditions.
         */
        public void setUpUsageGoal(final Goal goal, final Term[] updates,
                final Term[] assumptions) {
            final TermBuilder tb = services.getTermBuilder();
            goal.setBranchLabel("Usage");
            Term uAssumptions = tb.applySequential(updates, tb.and(assumptions));
            goal.addFormula(new SequentFormula(uAssumptions), true, false);
            goal.changeFormula(
                new SequentFormula(tb.applySequential(updates, buildUsageFormula(goal))),
                occurrence);
            TermLabelManager.refactorGoal(termLabelState, services, occurrence, application.rule(),
                goal, null, null);
        }

        /**
         *
         * @param block a block.
         * @return the block wrapped in a method frame if one is available, otherwise the block
         *         itself.
         */
        private Statement wrapInMethodFrameIfContextIsAvailable(final StatementBlock block) {
            if (instantiation.context == null) {
                return block;
            }
            return new MethodFrame(null, instantiation.context, block);
        }

        /**
         *
         * @param contract the contract being applied.
         * @param conditionVariable the variable used to store the loop guard's value.
         * @param exceptionParameter the exception variable.
         * @param breakFlags the break flags.
         * @param continueFlags the continue flags.
         * @return Java blocks for every program fragment.
         */
        private JavaBlock[] createJavaBlocks(final LoopContract contract,
                ProgramVariable conditionVariable, final ProgramVariable exceptionParameter,
                Map<Label, ProgramVariable> breakFlags, Map<Label, ProgramVariable> continueFlags) {
            AuxiliaryContract.Variables bodyVariables = new Variables(variables.self, breakFlags,
                continueFlags, variables.returnFlag, variables.result, variables.exception,
                variables.remembranceHeaps, variables.remembranceLocalVariables,
                variables.outerRemembranceHeaps, variables.outerRemembranceVariables, services);

            JavaBlock unfold = JavaBlock.createJavaBlock(new StatementBlock(
                wrapInMethodFrameIfContextIsAvailable(new ValidityProgramConstructor(labels,
                    new StatementBlock(
                        KeYJavaASTFactory.declare(conditionVariable, contract.getGuard())),
                    variables, exceptionParameter, services).construct())));

            JavaBlock body =
                JavaBlock.createJavaBlock(new StatementBlock(wrapInMethodFrameIfContextIsAvailable(
                    new ValidityProgramConstructor(labels, contract.getBody(), bodyVariables,
                        exceptionParameter, services, variables).construct())));

            JavaBlock tail = JavaBlock.createJavaBlock(new StatementBlock(
                finishTransactionIfModalityIsTransactional(wrapInMethodFrameIfContextIsAvailable(
                    new ValidityProgramConstructor(labels, contract.getTail(), variables,
                        exceptionParameter, services, variables).construct()))));
            return new JavaBlock[] { unfold, body, tail };
        }

        private StatementBlock finishTransactionIfModalityIsTransactional(
                final Statement statement) {
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

        private Term buildUsageFormula(Goal goal) {
            return services.getTermBuilder().prog(
                instantiation.modality, replaceBlock(instantiation.formula.javaBlock(),
                    instantiation.statement, constructAbruptTerminationIfCascade()),
                instantiation.formula.sub(0),
                TermLabelManager.instantiateLabels(termLabelState, services, occurrence,
                    application.rule(), application, goal, BlockContractHint.USAGE_BRANCH, null,
                    instantiation.modality, new ImmutableArray<>(instantiation.formula.sub(0)),
                    null, instantiation.formula.javaBlock(), instantiation.formula.getLabels()));
        }

        private JavaBlock replaceBlock(final JavaBlock java, final JavaStatement oldBlock,
                final StatementBlock newBlock) {
            Statement newProgram = (Statement) new ProgramElementReplacer(java.program(), services)
                    .replace(oldBlock, newBlock);
            return JavaBlock.createJavaBlock(
                newProgram instanceof StatementBlock ? (StatementBlock) newProgram
                        : new StatementBlock(newProgram));
        }

        private StatementBlock constructAbruptTerminationIfCascade() {
            List<If> ifCascade = new ArrayList<>();
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
                new NotEquals(
                    new ExtList(new Expression[] { variables.exception, NullLiteral.NULL })),
                KeYJavaASTFactory.throwClause(variables.exception)));
            return new StatementBlock(ifCascade.toArray(new Statement[0]));
        }

        private JavaBlock getJavaBlock(final ProgramVariable exceptionParameter) {
            final StatementBlock block;

            if (instantiation.statement instanceof StatementBlock) {
                block =
                    new ValidityProgramConstructor(labels, (StatementBlock) instantiation.statement,
                        variables, exceptionParameter, services).construct();
            } else {
                block = new ValidityProgramConstructor(labels,
                    new StatementBlock(instantiation.statement), variables, exceptionParameter,
                    services).construct();
            }

            Statement wrappedBlock = wrapInMethodFrameIfContextIsAvailable(block);
            StatementBlock finishedBlock = finishTransactionIfModalityIsTransactional(wrappedBlock);
            return JavaBlock.createJavaBlock(finishedBlock);
        }

        private Map<Label, ProgramVariable> collectContinueFlags(final LoopContract contract,
                ProgramVariable continuedLoopVariable, List<Continue> bodyContinues) {
            Map<Label, ProgramVariable> continueFlags =
                new LinkedHashMap<>(variables.continueFlags);
            continueFlags.remove(null);
            for (Continue cont : bodyContinues) {
                Label label = cont.getLabel();
                if (label == null || contract.getLoopLabels().contains(label)) {
                    continueFlags.put(label, continuedLoopVariable);
                }
            }
            return continueFlags;
        }

        private Term[] createPosts(final Goal goal, final Term[] postconditions,
                final Term[] postconditionsNext, final AuxiliaryContract.Terms terms,
                final TermBuilder tb) {
            Term post = tb.and(postconditions);
            post = AbstractOperationPO.addAdditionalUninterpretedPredicateIfRequired(services, post,
                ImmutableSLList.<LocationVariable>nil()
                        .prependReverse(terms.remembranceLocalVariables.keySet()),
                terms.exception);
            post = TermLabelManager.refactorTerm(termLabelState, services, null, post, rule, goal,
                AbstractAuxiliaryContractRule.NEW_POSTCONDITION_TERM_HINT, null);

            Term postNext = tb.and(postconditionsNext);
            postNext = AbstractOperationPO.addAdditionalUninterpretedPredicateIfRequired(services,
                postNext, ImmutableSLList.<LocationVariable>nil()
                        .prependReverse(terms.remembranceLocalVariables.keySet()),
                terms.exception);
            postNext = TermLabelManager.refactorTerm(termLabelState, services, null, postNext, rule,
                goal, AbstractAuxiliaryContractRule.NEW_POSTCONDITION_TERM_HINT, null);
            final Term[] posts = new Term[] { post, postNext };
            return posts;
        }
    }
}
