package de.uka.ilkd.key.rule;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.StatementContainer;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.BlockSpecificationElement;
import de.uka.ilkd.key.util.MiscTools;

/**
 * <p>Rule for the application of {@link BlockSpecificationElement}s.</p>
 *
 * @see AbstractBlockSpecificationElementBuiltInRuleApp
 */
public abstract class AbstractBlockSpecificationElementRule implements BuiltInRule {

    public static final String FULL_PRECONDITION_TERM_HINT = "fullPrecondition";
    public static final String NEW_POSTCONDITION_TERM_HINT = "newPostcondition";

    protected static boolean occursNotAtTopLevelInSuccedent(final PosInOccurrence occurrence) {
        return occurrence == null || !occurrence.isTopLevel() || occurrence.isInAntec();
    }

    /**
     * Adds {@code pv} to the {@code sevices}' program variable namespace.
     *
     * @param pv
     * @param services
     */
    protected static void register(ProgramVariable pv,
                         Services services) {
        Namespace<IProgramVariable> progVarNames = services.getNamespaces().programVariables();
        if (pv != null && progVarNames.lookup(pv.name()) == null) {
            progVarNames.addSafely(pv);
        }
    }

    public abstract Instantiation getLastInstantiation();
    public abstract Term getLastFocusTerm();

    protected abstract void setLastInstantiation(Instantiation result);
    protected abstract void setLastFocusTerm(Term formula);

    @Override
    public String displayName() {
        return name().toString();
    }

    @Override
    public String toString() {
        return name().toString();
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    protected static Term createLocalAnonUpdate(ImmutableSet<ProgramVariable> localOuts,
                                                Services services) {
        Term anonUpdate = null;
        final TermBuilder tb = services.getTermBuilder();
        for(ProgramVariable pv : localOuts) {
            final Name anonFuncName = new Name(tb.newName(pv.name().toString()));
            final Function anonFunc = new Function(anonFuncName, pv.sort(), true);
            services.getNamespaces().functions().addSafely(anonFunc);
            final Term elemUpd = tb.elementary((LocationVariable)pv, tb.func(anonFunc));
            if(anonUpdate == null) {
                anonUpdate = elemUpd;
            } else {
                anonUpdate = tb.parallel(anonUpdate, elemUpd);
            }
        }

        return anonUpdate == null
                ? services.getTermBuilder().skip()
                : anonUpdate;
    }

    protected static ProgramVariable createLocalVariable(final String nameBase,
                                                final KeYJavaType type,
                                                final Services services) {
        return KeYJavaASTFactory.localVariable(services.getVariableNamer()
                                .getTemporaryNameProposal(nameBase), type);
    }

    public static final class Instantiation {

        public final Term update;
        public final Term formula;
        public final Modality modality;
        public final Term self;
        public final StatementBlock block;
        public final ExecutionContext context;

        public Instantiation(final Term update, final Term formula,
                             final Modality modality, final Term self,
                             final StatementBlock block, final ExecutionContext context) {
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

        public boolean isTransactional() {
            return modality.transaction();
        }
    }

    /**
     * A builder for {@link Instantiation}s.
     */
    protected static abstract class Instantiator {

        private final Term formula;
        private final Goal goal;
        private final Services services;

        public Instantiator(final Term formula,
                            final Goal goal,
                            final Services services) {
            this.formula = formula;
            this.goal = goal;
            this.services = services;
        }

        public Instantiation instantiate() {
            final Term update = extractUpdate();
            final Term target = extractUpdateTarget();
            if (!(target.op() instanceof Modality)) {
                return null;
            }
            final Modality modality = (Modality) target.op();
            final StatementBlock block =
                    getFirstBlockInPrefixWithAtLeastOneApplicableContract(modality,
                                                                          target.javaBlock(),
                                                                          goal);
            if (block == null) {
                return null;
            }
            final MethodFrame frame =
                    JavaTools.getInnermostMethodFrame(target.javaBlock(), services);
            final Term self = extractSelf(frame);
            final ExecutionContext context = extractExecutionContext(frame);
            return new Instantiation(update, target, modality, self, block, context);
        }

        private Term extractUpdate() {
            if (formula.op() instanceof UpdateApplication) {
                return UpdateApplication.getUpdate(formula);
            } else {
                return services.getTermBuilder().skip();
            }
        }

        private Term extractUpdateTarget() {
            if (formula.op() instanceof UpdateApplication) {
                return UpdateApplication.getTarget(formula);
            } else {
                return formula;
            }
        }

        private Term extractSelf(final MethodFrame frame) {
            if (frame == null) {
                return null;
            }
            return MiscTools.getSelfTerm(frame, services);
        }

        private static ExecutionContext extractExecutionContext(final MethodFrame frame) {
            if (frame == null) {
                return null;
            }
            return (ExecutionContext) frame.getExecutionContext();
        }

        private StatementBlock
                    getFirstBlockInPrefixWithAtLeastOneApplicableContract(final Modality modality,
                                                                          final JavaBlock java,
                                                                          final Goal goal) {
            SourceElement element = java.program().getFirstElement();
            while ((element instanceof ProgramPrefix || element instanceof CatchAllStatement)
                    && !(element instanceof StatementBlock
                            && ((StatementBlock) element).isEmpty())) {
                if (element instanceof StatementBlock
                        && hasApplicableContracts(
                                services, (StatementBlock) element, modality, goal)) {
                    return (StatementBlock) element;
                } else if (element instanceof StatementContainer) {
                    element = ((StatementContainer) element).getStatementAt(0);
                } else {
                    element = element.getFirstElement();
                }
            }
            return null;
        }

        protected abstract boolean hasApplicableContracts(
                                               final Services services,
                                               final StatementBlock block,
                                               final Modality modality,
                                               Goal goal);
    }

}
