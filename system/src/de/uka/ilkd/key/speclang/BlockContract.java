package de.uka.ilkd.key.speclang;

import java.util.*;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.Break;
import de.uka.ilkd.key.java.statement.Continue;
import de.uka.ilkd.key.java.statement.LabelJumpStatement;
import de.uka.ilkd.key.java.visitor.OuterBreakContinueAndReturnCollector;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.util.MiscTools;

public interface BlockContract extends SpecificationElement {
    
	public StatementBlock getBlock();
    public IProgramMethod getMethod();
    public Modality getModality();
    public Variables getPlaceholderVariables();
    public boolean getTransaction();

    // TODO Why do we need remembranceHeaps for the precondition? Do we also need remembranceLocalVariables?
    public Term getPrecondition(LocationVariable heap,
                                ProgramVariable self,
                                Map<LocationVariable, LocationVariable> remembranceHeaps,
                                Services services);
    public Term getPrecondition(LocationVariable heapVariable,
                                Term heap,
                                Term self,
                                Map<LocationVariable, Term> remembranceHeaps,
                                Services services);
    public Term getPrecondition(LocationVariable heap, Services services);

    public Term getPostcondition(LocationVariable heap, Variables variables, Services services);
    public Term getPostcondition(LocationVariable heapVariable, Term heap, Terms terms, Services services);
    public Term getPostcondition(LocationVariable heap, Services services);

    public Term getModifiesCondition(LocationVariable heap, ProgramVariable self, Services services);
    public Term getModifiesCondition(LocationVariable heapVariable, Term heap, Term self, Services services);
    public Term getModifiesCondition(LocationVariable heap, Services services);

    public void visit(Visitor visitor);

    public String getHtmlText(Services services);

    // TODO I'd like to remve the following method.
    public BlockContract update(StatementBlock newBlock,
                                Map<LocationVariable,Term> newPres,
                                Map<LocationVariable,Term> newPosts,
                                Map<LocationVariable,Term> newMods);

    public static class Variables {

        public static Variables create(StatementBlock block, IProgramMethod method, Services services)
        {
            return new VariablesCreator(block, method, services).create();
        }

        public final ProgramVariable self;
        public final Map<Label, ProgramVariable> breakFlags;
        public final Map<Label, ProgramVariable> continueFlags;
        public final ProgramVariable returnFlag;
        public final ProgramVariable result;
        public final ProgramVariable exception;
        public final Map<LocationVariable, LocationVariable> remembranceHeaps;
        public final Map<LocationVariable, LocationVariable> remembranceLocalVariables;

        public Variables(final ProgramVariable self,
                         final Map<Label, ProgramVariable> breakFlags,
                         final Map<Label, ProgramVariable> continueFlags,
                         final ProgramVariable returnFlag,
                         final ProgramVariable result,
                         final ProgramVariable exception,
                         final Map<LocationVariable, LocationVariable> remembranceHeaps,
                         final Map<LocationVariable, LocationVariable> remembranceLocalVariables)
        {
            this.self = self;
            this.breakFlags = breakFlags;
            this.continueFlags = continueFlags;
            this.returnFlag = returnFlag;
            this.result = result;
            this.exception = exception;
            this.remembranceHeaps = remembranceHeaps;
            this.remembranceLocalVariables = remembranceLocalVariables;
        }

        public Map<LocationVariable, LocationVariable> combineRemembranceVariables()
        {
            final Map<LocationVariable, LocationVariable> result = new LinkedHashMap<LocationVariable, LocationVariable>();
            result.putAll(remembranceHeaps);
            result.putAll(remembranceLocalVariables);
            return result;
        }

    }

    public static class VariablesCreator extends TermBuilder
    {

        private static final String REMEMBRANCE_SUFFIX = "BeforeBlock";

        private final StatementBlock block;
        private final IProgramMethod method;
        private Map<Label, ProgramVariable> breakFlags;
        private Map<Label, ProgramVariable> continueFlags;
        private ProgramVariable returnFlag;

        public VariablesCreator(final StatementBlock block, IProgramMethod method, final Services services)
        {
            super(services);
            this.block = block;
            this.method = method;
        }

        public Variables create()
        {
            createAndStoreFlags();
            return new Variables(
                selfVar(method, method.getContainerType(), false),
                breakFlags,
                continueFlags,
                returnFlag,
                resultVar(method, false),
                excVar(method, false),
                createRemembranceHeaps(),
                createRemembranceLocalVariables()
            );
        }

        private void createAndStoreFlags()
        {
            final OuterBreakContinueAndReturnCollector collector = new OuterBreakContinueAndReturnCollector(block, services);
            collector.collect();

            final List<Break> breaks = collector.getBreaks();
            final List<Continue> continues = collector.getContinues();
            final boolean returnOccurred = collector.hasReturns();

            final Set<Label> breakLabels = collectLabels(breaks);
            final Set<Label> continueLabels = collectLabels(continues);

            breakFlags = createFlags(breakLabels, "broke");
            continueFlags = createFlags(continueLabels, "continued");
            returnFlag = returnOccurred ? createFlag("returned") : null;
        }

        private Set<Label> collectLabels(final List<? extends LabelJumpStatement> jumps)
        {
            final Set<Label> result = new LinkedHashSet<Label>();
            for (LabelJumpStatement jump : jumps) {
                result.add(jump.getLabel());
            }
            return result;
        }

        private Map<Label, ProgramVariable> createFlags(final Set<Label> labels, final String baseName)
        {
            final Map<Label, ProgramVariable> result = new LinkedHashMap<Label, ProgramVariable>();
            for (Label label : labels) {
                final String suffix = label == null ? "" : "To" + label;
                result.put(label, createFlag(baseName + suffix));
            }
            return result;
        }

        private ProgramVariable createFlag(final String name)
        {
            return createVariable(name, services.getJavaInfo().getKeYJavaType("boolean"));
        }

        private Map<LocationVariable, LocationVariable> createRemembranceHeaps()
        {
            final Map<LocationVariable, LocationVariable> result = new LinkedHashMap<LocationVariable, LocationVariable>();
            for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                result.put(heap, heapAtPreVar(heap + REMEMBRANCE_SUFFIX, heap.sort(), false));
            }
            return result;
        }

        private Map<LocationVariable, LocationVariable> createRemembranceLocalVariables()
        {
            Map<LocationVariable, LocationVariable> result = new LinkedHashMap<LocationVariable, LocationVariable>();
            ImmutableSet<ProgramVariable> localOutVariables = MiscTools.getLocalOuts(block, services);
            for (ProgramVariable localOutVariable : localOutVariables) {
                result.put(
                    (LocationVariable) localOutVariable,
                    createVariable(localOutVariable.name() + REMEMBRANCE_SUFFIX, localOutVariable.getKeYJavaType())
                );
            }
            return result;
        }

        private LocationVariable createVariable(final String name, KeYJavaType type)
        {
            return new LocationVariable(new ProgramElementName(name), type);
        }

    }

    public static class Terms {

        public final Term self;
        public final Map<Label, Term> breakFlags;
        public final Map<Label, Term> continueFlags;
        public final Term returnFlag;
        public final Term result;
        public final Term exception;
        public final Map<LocationVariable, Term> remembranceHeaps;
        public final Map<LocationVariable, Term> remembranceLocalVariables;

        public Terms(final Term self,
                     final Map<Label, Term> breakFlags,
                     final Map<Label, Term> continueFlags,
                     final Term returnFlag,
                     final Term result,
                     final Term exception,
                     final Map<LocationVariable, Term> remembranceHeaps,
                     final Map<LocationVariable, Term> remembranceLocalVariables)
        {
            this.self = self;
            this.breakFlags = breakFlags;
            this.continueFlags = continueFlags;
            this.returnFlag = returnFlag;
            this.result= result;
            this.exception= exception;
            this.remembranceHeaps = remembranceHeaps;
            this.remembranceLocalVariables = remembranceLocalVariables;
        }

    }

}