package de.uka.ilkd.key.speclang;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.LoopInitializer;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.Break;
import de.uka.ilkd.key.java.statement.Continue;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.LabelJumpStatement;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.visitor.OuterBreakContinueAndReturnCollector;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.Contract.OriginalVariables;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.MiscTools;

/**
 * Super-interface for {@link BlockContract} and {@link LoopContract}.
 */
public interface BlockSpecificationElement extends SpecificationElement {

    public StatementBlock getBlock();
    public List<Label> getLabels();
    public IProgramMethod getMethod();
    public Modality getModality();
    public Variables getPlaceholderVariables();
    public boolean isTransactionApplicable();
    public boolean isReadOnly(Services services);
    public String getBaseName();

    /**
     * Returns <code>true</code> iff the method (according to the contract) does
     * not modify the heap at all, i.e., iff it is "strictly pure."
     *
     * @return whether this contract is strictly pure.
     */
    public boolean hasModifiesClause(LocationVariable heap);

    Term getInstantiationSelfTerm();

    public Term getPrecondition(LocationVariable heap,
                                ProgramVariable self,
                                Map<LocationVariable, LocationVariable> atPres,
                                Services services);
    public Term getPrecondition(LocationVariable heapVariable,
                                Term heap,
                                Term self,
                                Map<LocationVariable, Term> atPres,
                                Services services);
    public Term getPrecondition(LocationVariable heap, Services services);
    public Term getPrecondition(LocationVariable heap, Variables variables, Services services);
    public Term getPrecondition(LocationVariable heapVariable, Term heap,
            Terms terms, Services services);

    public Term getPostcondition(LocationVariable heap, Variables variables, Services services);
    public Term getPostcondition(LocationVariable heapVariable, Term heap,
                                 Terms terms, Services services);
    public Term getPostcondition(LocationVariable heap, Services services);

    public Term getModifiesClause(LocationVariable heap, ProgramVariable self, Services services);
    public Term getModifiesClause(LocationVariable heapVariable, Term heap,
                                  Term self, Services services);
    public Term getModifiesClause(LocationVariable heap, Services services);

    public Term getRequires(LocationVariable heap);

    public Term getEnsures(LocationVariable heap);

    public Term getAssignable(LocationVariable heap);

    public void visit(Visitor visitor);

    public String getUniqueName();

    public String getHtmlText(Services services);

    public String getPlainText(Services services);

    public String getPlainText(Services services, Terms terms);

    /**
     * Returns the method in which the block is located.
     */
    public IProgramMethod getTarget();

    /**
     * Tells whether the contract contains a measured_by clause.
     */
    public boolean hasMby();

    public Term getMby();

    Term getMby(Variables variables, Services services);

    public Term getMby(ProgramVariable selfVar, Services services);

    public Term getMby(Map<LocationVariable, Term> heapTerms, Term selfTerm,
            Map<LocationVariable, Term> atPres, Services services);

    public boolean hasInfFlowSpecs();

    public void setInstantiationSelf(Term selfInstantiation);

    /**
     * Returns the term internally used for self or a newly instantiated one.
     * Use with care - it is likely that this is *not* the right "self" for you.
     */
    public Term getInstantiationSelfTerm(TermServices services);

    /**
     * Returns the original precondition of the contract.
     */
    Term getPre(Services services);

    /**
     * Returns the original postcondition of the contract.
     */
    Term getPost(Services services);

    /**
     * Returns the original modifies clause of the contract.
     */
    Term getMod(Services services);

    /**
     * Returns the original information flow specification clause of the contract.
     */
    public ImmutableList<InfFlowSpec> getInfFlowSpecs();

    /**
     * Returns the original used variables like self, result etc..
     */
    public Variables getVariables();
    public BlockSpecificationElement setTarget(KeYJavaType newKJT, IObserverFunction newPM);
    public BlockSpecificationElement setBlock(StatementBlock newBlock);

    /**
     * Returns the original used variables like self, result etc. as terms.
     */
    public Terms getVariablesAsTerms(Services services);

    public OriginalVariables getOrigVars();

    /**
     * This class contains all new variables that are introduced during a
     * {@link BlockSpecificationElement}'s instantiation.
     */
    public static class Variables {
        public final ProgramVariable self;
        public final Map<Label, ProgramVariable> breakFlags;
        public final Map<Label, ProgramVariable> continueFlags;
        public final ProgramVariable returnFlag;
        public final ProgramVariable result;
        public final ProgramVariable exception;

        /**
         * A map from every heap {@code heap} to {@code heap_Before_BLOCK}.
         */
        public final Map<LocationVariable, LocationVariable> remembranceHeaps;

        /**
         * A map from every variable {@code var} that is assignable inside the block
         * to {@code var_Before_BLOCK}.
         */
        public final Map<LocationVariable, LocationVariable> remembranceLocalVariables;

        /**
         * A map from every heap {@code heap} that is accessible
         * inside the block to {@code heap_Before_METHOD}.
         */
        public final Map<LocationVariable, LocationVariable> outerRemembranceHeaps;

        /**
         * A map from every variable {@code var} that is accessible
         * inside the block to {@code var_Before_METHOD}.
         */
        public final Map<LocationVariable, LocationVariable> outerRemembranceVariables;

        private final TermServices services;

        public Variables(final ProgramVariable self,
                         final Map<Label, ProgramVariable> breakFlags,
                         final Map<Label, ProgramVariable> continueFlags,
                         final ProgramVariable returnFlag,
                         final ProgramVariable result,
                         final ProgramVariable exception,
                         final Map<LocationVariable, LocationVariable> remembranceHeaps,
                         final Map<LocationVariable, LocationVariable> remembranceLocalVariables,
                         final Map<LocationVariable, LocationVariable>
                             outerRemembranceHeaps,
                         final Map<LocationVariable, LocationVariable>
                                 outerRemembranceVariables,
                         final TermServices services) {
            this.services = services;
            this.self = self;
            this.breakFlags = breakFlags;
            this.continueFlags = continueFlags;
            this.returnFlag = returnFlag;
            this.result = result;
            this.exception = exception;
            this.remembranceHeaps = remembranceHeaps;
            this.remembranceLocalVariables = remembranceLocalVariables;
            this.outerRemembranceHeaps = outerRemembranceHeaps;
            this.outerRemembranceVariables = outerRemembranceVariables;
        }

        public static Variables create(final StatementBlock block,
                                       final List<Label> labels,
                                       final IProgramMethod method,
                                       final Services services) {
            return new VariablesCreator(block, labels, method, services).create();
        }

        public Map<LocationVariable, LocationVariable> combineRemembranceVariables() {
            final Map<LocationVariable, LocationVariable> result =
                    new LinkedHashMap<LocationVariable, LocationVariable>();
            result.putAll(remembranceHeaps);
            result.putAll(remembranceLocalVariables);
            return result;
        }

        public Map<LocationVariable, LocationVariable> combineOuterRemembranceVariables() {
            final Map<LocationVariable, LocationVariable> result =
                    new LinkedHashMap<LocationVariable, LocationVariable>();
            result.putAll(outerRemembranceHeaps);
            result.putAll(outerRemembranceVariables);
            return result;
        }

        public Terms termify(Term self) {
            return new Terms(
                self,
                termifyFlags(breakFlags),
                termifyFlags(continueFlags),
                termifyVariable(returnFlag),
                termifyVariable(result),
                termifyVariable(exception),
                termifyRemembranceVariables(remembranceHeaps),
                termifyRemembranceVariables(remembranceLocalVariables),
                termifyRemembranceVariables(outerRemembranceHeaps),
                termifyRemembranceVariables(outerRemembranceVariables)
            );
        }

        private Map<Label, Term> termifyFlags(final Map<Label, ProgramVariable> flags) {
            final Map<Label, Term> result = new LinkedHashMap<Label, Term>();
            for (Map.Entry<Label, ProgramVariable> flag : flags.entrySet()) {
                result.put(flag.getKey(), termifyVariable(flag.getValue()));
            }
            return result;
        }

        private Map<LocationVariable, Term> termifyRemembranceVariables(
                    final Map<LocationVariable, LocationVariable> remembranceVariables) {
            final Map<LocationVariable, Term> result = new LinkedHashMap<LocationVariable, Term>();
            for (Map.Entry<LocationVariable, LocationVariable> remembranceVariable
                    : remembranceVariables.entrySet()) {
                result.put(remembranceVariable.getKey(),
                           termifyVariable(remembranceVariable.getValue()));
            }
            return result;
        }

        private Term termifyVariable(final ProgramVariable variable) {
            if (variable != null) {
                return services.getTermBuilder().var(variable);
            } else {
                return null;
            }
        }

        /* (non-Javadoc)
         * @see java.lang.Object#hashCode()
         */
        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result
                    + ((breakFlags == null) ? 0 : breakFlags.hashCode());
            result = prime * result
                    + ((continueFlags == null) ? 0 : continueFlags.hashCode());
            result = prime * result
                    + ((exception == null) ? 0 : exception.hashCode());
            result = prime
                    * result
                    + ((remembranceHeaps == null) ? 0 : remembranceHeaps
                            .hashCode());
            result = prime
                    * result
                    + ((remembranceLocalVariables == null) ? 0
                            : remembranceLocalVariables.hashCode());
            result = prime * result
                    + ((this.result == null) ? 0 : this.result.hashCode());
            result = prime * result
                    + ((returnFlag == null) ? 0 : returnFlag.hashCode());
            result = prime * result + ((self == null) ? 0 : self.hashCode());
            return result;
        }

        /* (non-Javadoc)
         * @see java.lang.Object#equals(java.lang.Object)
         */
        @Override
        public boolean equals(Object obj) {
            if (this == obj) {
                return true;
            } else if (obj == null || getClass() != obj.getClass()) {
                return false;
            }
            Variables other = (Variables) obj;
            if (breakFlags == null && other.breakFlags != null) {
                return false;
            } else if (breakFlags != null && !breakFlags.equals(other.breakFlags)) {
                return false;
            } else if (continueFlags == null && other.continueFlags != null) {
                return false;
            } else if (continueFlags != null && !continueFlags.equals(other.continueFlags)) {
                return false;
            } else if (exception == null && other.exception != null) {
                return false;
            } else if (exception != null && !exception.equals(other.exception)) {
                return false;
            } else if (remembranceHeaps == null && other.remembranceHeaps != null) {
                return false;
            } else if (remembranceHeaps != null
                         && !remembranceHeaps.equals(other.remembranceHeaps)) {
                return false;
            } else if (remembranceLocalVariables == null
                         && other.remembranceLocalVariables != null) {
                return false;
            } else if (remembranceLocalVariables != null
                         && !remembranceLocalVariables.equals(other.remembranceLocalVariables)) {
                return false;
            } else if (outerRemembranceVariables == null
                         && other.outerRemembranceVariables != null) {
                return false;
            } else if (outerRemembranceVariables != null
                         && !outerRemembranceVariables.equals(other.outerRemembranceVariables)) {
                return false;
            } else if (result == null && other.result != null) {
                return false;
            } else if (result != null && !result.equals(other.result)) {
                return false;
            } else if (returnFlag == null && other.returnFlag != null) {
                return false;
            } else if (returnFlag != null && !returnFlag.equals(other.returnFlag)) {
                return false;
            } else if (self == null && other.self != null) {
                return false;
            } else if (self != null && !self.equals(other.self)) {
                return false;
            }
            return true;
        }

        public OriginalVariables toOrigVars() {
            Map<LocationVariable, ProgramVariable> atPreVars =
                    new LinkedHashMap<LocationVariable, ProgramVariable>();
            for (LocationVariable h: remembranceLocalVariables.keySet()) {
                atPreVars.put(h, remembranceLocalVariables.get(h));
            }
            return new OriginalVariables(self, result,
                                         exception, atPreVars,
                                         ImmutableSLList.<ProgramVariable>nil());
        }

    }

    /**
     * @see Variables#create(StatementBlock, List, IProgramMethod, Services)
     */
    public static class VariablesCreator extends TermBuilder {

        private static final String BREAK_FLAG_BASE_NAME = "broke";
        private static final String CONTINUE_FLAG_BASE_NAME = "continued";
        private static final String RETURN_FLAG_NAME = "returned";
        private static final String FLAG_INFIX = "To";
        private static final String REMEMBRANCE_SUFFIX = "_Before_BLOCK";
        private static final String OUTER_REMEMBRANCE_SUFFIX = "_Before_METHOD";

        private final StatementBlock block;
        private final List<Label> labels;
        private final IProgramMethod method;
        private Map<Label, ProgramVariable> breakFlags;
        private Map<Label, ProgramVariable> continueFlags;
        private ProgramVariable returnFlag;

        public VariablesCreator(final StatementBlock block, final List<Label> labels,
                                final IProgramMethod method, final Services services) {
            super(services.getTermFactory(), services);
            this.block = block;
            this.labels = labels;
            this.method = method;
        }

        public Variables create() {
            createAndStoreFlags();

            return new Variables(
                selfVar(method, method.getContainerType(), false),
                breakFlags,
                continueFlags,
                returnFlag,
                resultVar(services.getVariableNamer()
                        .getTemporaryNameProposal("result").toString(), method, false),
                excVar(services.getVariableNamer()
                        .getTemporaryNameProposal("exc").toString(), method, false),
                createRemembranceHeaps(),
                createRemembranceLocalVariables(),
                createOuterRemembranceHeaps(),
                createOuterRemembranceLocalVariables(),
                services
            );
        }

        private void createAndStoreFlags() {
            final OuterBreakContinueAndReturnCollector collector =
                    new OuterBreakContinueAndReturnCollector(block, labels, services);
            collector.collect();

            final List<Break> breaks = collector.getBreaks();
            final List<Continue> continues = collector.getContinues();
            final boolean returnOccurred = collector.hasReturns();

            final Set<Label> breakLabels = collectLabels(breaks);
            final Set<Label> continueLabels = collectLabels(continues);

            breakFlags = createFlags(breakLabels, BREAK_FLAG_BASE_NAME);
            continueFlags = createFlags(continueLabels, CONTINUE_FLAG_BASE_NAME);
            returnFlag = returnOccurred ? createFlag(RETURN_FLAG_NAME) : null;
        }

        private Set<Label> collectLabels(final List<? extends LabelJumpStatement> jumps) {
            final Set<Label> result = new LinkedHashSet<Label>();
            for (LabelJumpStatement jump : jumps) {
                result.add(jump.getLabel());
            }
            return result;
        }

        private Map<Label, ProgramVariable> createFlags(final Set<Label> labels,
                                                        final String baseName) {
            final Map<Label, ProgramVariable> result = new LinkedHashMap<Label, ProgramVariable>();
            for (Label label : labels) {
                final String suffix = label == null ? "" : FLAG_INFIX + label;
                result.put(label, createFlag(baseName + suffix));
            }
            return result;
        }

        private ProgramVariable createFlag(final String name) {
            return createVariable(name, services.getJavaInfo().getKeYJavaType("boolean"));
        }

        private Map<LocationVariable, LocationVariable> createRemembranceHeaps() {
            return createRemembranceHeaps(REMEMBRANCE_SUFFIX);
        }

        private Map<LocationVariable, LocationVariable> createRemembranceHeaps(String suffix) {
            final Map<LocationVariable, LocationVariable> result =
                    new LinkedHashMap<LocationVariable, LocationVariable>();
            for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                result.put(heap, heapAtPreVar(heap + suffix, heap.sort(), false));
            }
            return result;
        }

        private Map<LocationVariable, LocationVariable> createRemembranceLocalVariables() {
            ImmutableSet<ProgramVariable> localOutVariables =
                MiscTools.getLocalOuts(block, services);

            SourceElement first = block.getFirstElement();
            while (first instanceof LabeledStatement) {
                LabeledStatement s = (LabeledStatement) first;
                first = s.getBody();
            }

            if (first instanceof For) {
                ImmutableArray<LoopInitializer> inits = ((For) first).getInitializers();
                ProgramVariableCollector collector =
                    new ProgramVariableCollector(new StatementBlock(inits), services);
                collector.start();

                for (LocationVariable var : collector.result()) {
                    if (!var.getKeYJavaType()
                            .equals(services.getTypeConverter()
                            .getHeapLDT().getHeap().getKeYJavaType())) {
                        localOutVariables = localOutVariables.add(var);
                    }
                }
            }

            Map<LocationVariable, LocationVariable> result =
                new LinkedHashMap<LocationVariable, LocationVariable>();

            for (ProgramVariable var : localOutVariables) {
                result.put(
                    (LocationVariable) var,
                    createVariable(var.name() + REMEMBRANCE_SUFFIX, var.getKeYJavaType())
                );
            }
            return result;
        }

        private Map<LocationVariable, LocationVariable> createOuterRemembranceHeaps() {
            return createRemembranceHeaps(OUTER_REMEMBRANCE_SUFFIX);
        }

        private Map<LocationVariable, LocationVariable> createOuterRemembranceLocalVariables() {
            ImmutableSet<ProgramVariable> localInVariables =
                MiscTools.getLocalIns(block, services);

            SourceElement first = block.getFirstElement();
            while (first instanceof LabeledStatement) {
                LabeledStatement s = (LabeledStatement) first;
                first = s.getBody();
            }

            if (first instanceof For) {
                ImmutableArray<LoopInitializer> inits = ((For) first).getInitializers();
                ProgramVariableCollector collector =
                    new ProgramVariableCollector(new StatementBlock(inits), services);
                collector.start();

                for (LocationVariable var : collector.result()) {
                    if (!var.getKeYJavaType()
                            .equals(services.getTypeConverter()
                                .getHeapLDT().getHeap().getKeYJavaType())) {
                        localInVariables = localInVariables.add(var);
                    }
                }
            }

            Map<LocationVariable, LocationVariable> result =
                new LinkedHashMap<LocationVariable, LocationVariable>();

            for (ProgramVariable var : localInVariables) {
                result.put(
                        (LocationVariable) var,
                        createVariable(var.name() + OUTER_REMEMBRANCE_SUFFIX,
                                       var.getKeYJavaType()));
            }
            return result;
        }

        private LocationVariable createVariable(final String name, final KeYJavaType type) {
            return new LocationVariable(services.getVariableNamer()
                    .getTemporaryNameProposal(name), type);
        }
    }

    /**
     * @see Variables#termify(Term)
     */
    public static class Terms {

        public final Term self;
        public final Map<Label, Term> breakFlags;
        public final Map<Label, Term> continueFlags;
        public final Term returnFlag;
        public final Term result;
        public final Term exception;
        public final Map<LocationVariable, Term> remembranceHeaps;
        public final Map<LocationVariable, Term> remembranceLocalVariables;
        public final Map<LocationVariable, Term> outerRemembranceHeaps;
        public final Map<LocationVariable, Term> outerRemembranceVariables;

        public Terms(final Term self,
                     final Map<Label, Term> breakFlags,
                     final Map<Label, Term> continueFlags,
                     final Term returnFlag,
                     final Term result,
                     final Term exception,
                     final Map<LocationVariable, Term> remembranceHeaps,
                     final Map<LocationVariable, Term> remembranceLocalVariables,
                     final Map<LocationVariable, Term> outerRemembranceHeaps,
                     final Map<LocationVariable, Term> outerRemembranceVariables) {
            this.self = self;
            this.breakFlags = breakFlags;
            this.continueFlags = continueFlags;
            this.returnFlag = returnFlag;
            this.result = result;
            this.exception = exception;
            this.remembranceHeaps = remembranceHeaps;
            this.remembranceLocalVariables = remembranceLocalVariables;
            this.outerRemembranceHeaps = outerRemembranceHeaps;
            this.outerRemembranceVariables = outerRemembranceVariables;
        }

        public Terms(Variables variables, TermBuilder tb) {
            this(tb.var(variables.self),
                 convertFlagMap(variables.breakFlags, tb),
                 convertFlagMap(variables.continueFlags, tb),
                 tb.var(variables.returnFlag),
                 tb.var(variables.result),
                 tb.var(variables.exception),
                 convertHeapMap(variables.remembranceHeaps, tb),
                 convertHeapMap(variables.remembranceLocalVariables, tb),
                 convertHeapMap(variables.outerRemembranceHeaps, tb),
                 convertHeapMap(variables.outerRemembranceVariables, tb));
        }

        private static Map<LocationVariable, Term> convertHeapMap(
                Map<LocationVariable, LocationVariable> map, TermBuilder tb) {
            return map.entrySet().stream().collect(
                    Collectors.<Map.Entry<LocationVariable, LocationVariable>,
                        LocationVariable, Term>toMap(
                            Map.Entry::getKey,
                        entry -> tb.var(entry.getValue())
                    )
           );
        }

        private static Map<Label, Term> convertFlagMap(
                Map<Label, ProgramVariable> map, TermBuilder tb) {
            return map.entrySet().stream().collect(
                            Collectors.<Map.Entry<Label, ProgramVariable>, Label, Term>toMap(
                                    Map.Entry::getKey,
                                entry -> tb.var(entry.getValue())
                            )
                   );
        }
    }
}
