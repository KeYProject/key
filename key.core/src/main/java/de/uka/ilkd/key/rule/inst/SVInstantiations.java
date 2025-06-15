/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.inst;

import java.util.Iterator;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.util.Debug;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.instantiation.IllegalInstantiationException;
import org.key_project.prover.rules.instantiation.InstantiationEntry;
import org.key_project.prover.rules.instantiation.ListInstantiation;
import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableMapEntry;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.logic.equality.IrrelevantTermLabelsProperty.IRRELEVANT_TERM_LABELS_PROPERTY;

/**
 * This class wraps an {@link ImmutableMap} from {@link SchemaVariable} to
 * {@link InstantiationEntry}
 * and is used to store instantiations of schemavariables. The class is immutable,
 * this means changing its content results in creating a new object.
 */
public class SVInstantiations
        implements org.key_project.prover.rules.instantiation.SVInstantiations {
    /** the empty instantiation */
    public static final SVInstantiations EMPTY_SVINSTANTIATIONS = new SVInstantiations();

    /**
     * the context itself is not realised as a schemavariable, therefore we need here a dummy SV for
     * a more unified handling (key in map)
     */
    private static final SchemaVariable CONTEXTSV = SchemaVariableFactory.createProgramSV(
        new ProgramElementName("Context"), new ProgramSVSort(new Name("ContextStatementBlock")) {
            public boolean canStandFor(ProgramElement pe, Services services) {
                return true;
            }
        }, false); // just a dummy SV for context


    /** the map with the instantiations to logic terms */
    private final ImmutableMap<SchemaVariable, InstantiationEntry<?>> map;

    /**
     * just a list of "interesting" instantiations: these instantiations are not 100% predetermined
     * and worth saving in a proof
     */
    private final ImmutableMap<SchemaVariable, InstantiationEntry<?>> interesting;

    /**
     * updates may be ignored when matching, therefore they need to be added after the application
     * around the added/replaced parts. These are stored in this list
     */
    private final ImmutableList<UpdateLabelPair> updateContext;

    /** instantiations of generic sorts */
    private GenericSortInstantiations genericSortInstantiations =
        GenericSortInstantiations.EMPTY_INSTANTIATIONS;

    /** additional conditions for the generic sorts */
    private final ImmutableList<GenericSortCondition> genericSortConditions;

    /** creates a new SVInstantions object with an empty map */
    private SVInstantiations() {
        genericSortConditions = ImmutableSLList.nil();
        updateContext = ImmutableSLList.nil();
        map = DefaultImmutableMap.nilMap();
        interesting = DefaultImmutableMap.nilMap();
    }

    /**
     * creates a new SVInstantions object using the given map
     *
     * @param map the ImmMap<SchemaVariable,InstantiationEntry<?>> with the instantiations
     */
    private SVInstantiations(ImmutableMap<SchemaVariable, InstantiationEntry<?>> map,
            ImmutableMap<SchemaVariable, InstantiationEntry<?>> interesting,
            ImmutableList<UpdateLabelPair> updateContext,
            ImmutableList<GenericSortCondition> genericSortConditions) {
        this(map, interesting, updateContext, GenericSortInstantiations.EMPTY_INSTANTIATIONS,
            genericSortConditions);
    }

    private SVInstantiations(ImmutableMap<SchemaVariable, InstantiationEntry<?>> map,
            ImmutableMap<SchemaVariable, InstantiationEntry<?>> interesting,
            ImmutableList<UpdateLabelPair> updateContext,
            GenericSortInstantiations genericSortInstantiations,
            ImmutableList<GenericSortCondition> genericSortConditions) {
        this.map = map;
        this.interesting = interesting;
        this.updateContext = updateContext;
        this.genericSortInstantiations = genericSortInstantiations;
        this.genericSortConditions = genericSortConditions;
    }


    public GenericSortInstantiations getGenericSortInstantiations() {
        return genericSortInstantiations;
    }


    public ImmutableList<GenericSortCondition> getGenericSortConditions() {
        return genericSortConditions;
    }

    /**
     * adds the given pair to the instantiations. If the given SchemaVariable has been instantiated
     * already, the new pair is taken without a warning.
     *
     * @param sv the SchemaVariable to be instantiated
     * @param matchedElement the SyntaxElement the SchemaVariable is instantiated with
     * @return SVInstantiations the new SVInstantiations containing the given pair
     */
    public SVInstantiations add(SchemaVariable sv, SyntaxElement matchedElement,
            LogicServices services) throws SortException {
        return add(sv, new InstantiationEntry<>(matchedElement), services);
    }

    public SVInstantiations addInteresting(SchemaVariable sv, JTerm subst, LogicServices services) {
        return addInteresting(sv, new InstantiationEntry<>(subst), services);
    }

    public <T> SVInstantiations add(SchemaVariable sv, ImmutableArray<T> pes, Class<T> type,
            LogicServices services) {
        return add(sv, new ListInstantiation(pes, type), services);
    }

    public SVInstantiations addInteresting(SchemaVariable sv, ProgramElement pe,
            LogicServices services) {
        return addInteresting(sv, new InstantiationEntry<>(pe), services);
    }

    /**
     * adds the given pair to the instantiations for the context.If the context has been
     * instantiated already, the new pair is taken without a warning.
     *
     * @param prefix the PosInProgram describing the prefix
     * @param postfix the PosInProgram describing the postfix
     * @param activeStatementContext the ExecutionContext of the first active statement
     * @param pe the ProgramElement the context positions are related to
     * @return SVInstantiations the new SVInstantiations containing the given pair
     */
    public SVInstantiations add(PosInProgram prefix, PosInProgram postfix,
            ExecutionContext activeStatementContext, ProgramElement pe, LogicServices services) {
        return add(CONTEXTSV,
            new InstantiationEntry<>(new ContextStatementBlockInstantiation(prefix, postfix,
                activeStatementContext, pe)),
            services);
    }


    // the following two exceptions are created statically for performance
    private static final SortException INCOMPATIBLE_INSTANTIATION_EXCEPTION =
        new SortException("Sort of SV " + "is not compatible with its " + "instantiation's sort\n"
            + "(This exception object is static)");

    private static final IllegalInstantiationException CONVERT_INSTANTIATION_EXCEPTION =
        new SortException("Instantiation of SV " + "cannot be converted to logic\n"
            + "(This exception object is static)");

    private static final SortException UNSOLVABLE_SORT_CONDITIONS_EXCEPTION = new SortException(
        "Conditions for sorts" + " cannot be satisfied\n" + "(This exception object is static)");

    private SVInstantiations checkSorts(SchemaVariable p_sv, InstantiationEntry<?> p_entry,
            boolean p_forceRebuild, LogicServices services) {
        if (p_sv instanceof JOperatorSV asv) {
            Boolean b = getGenericSortInstantiations().checkSorts(asv, p_entry);

            if (b == null) {
                return rebuildSorts(services);
            } else if (!b) {
                throw INCOMPATIBLE_INSTANTIATION_EXCEPTION;
            }
            if (p_forceRebuild) {
                return rebuildSorts(services);
            }
        }
        return this;
    }

    private SVInstantiations checkCondition(GenericSortCondition p_c, boolean p_forceRebuild,
            LogicServices services) {
        Boolean b = getGenericSortInstantiations().checkCondition(p_c);

        if (b == null) {
            return rebuildSorts(services);
        } else if (!b) {
            throw UNSOLVABLE_SORT_CONDITIONS_EXCEPTION;
        }
        if (p_forceRebuild) {
            return rebuildSorts(services);
        }
        return this;
    }

    private SVInstantiations rebuildSorts(LogicServices services) {
        genericSortInstantiations =
            GenericSortInstantiations.create(map.iterator(), getGenericSortConditions(), services);
        return this;
    }

    /**
     * adds the given pair to the instantiations. If the given SchemaVariable has been instantiated
     * already, the new pair is taken without a warning.
     *
     * @param sv the SchemaVariable to be instantiated
     * @param entry the InstantiationEntry
     * @return SVInstantiations the new SVInstantiations containing the given pair
     */
    public SVInstantiations add(SchemaVariable sv, InstantiationEntry<?> entry,
            LogicServices services) {
        return new SVInstantiations(map.put(sv, entry), interesting(), getUpdateContext(),
            getGenericSortInstantiations(), getGenericSortConditions()).checkSorts(sv, entry, false,
                services);
    }

    public SVInstantiations addInteresting(SchemaVariable sv, InstantiationEntry<?> entry,
            LogicServices services) {
        return new SVInstantiations(map.put(sv, entry), interesting().put(sv, entry),
            getUpdateContext(), getGenericSortInstantiations(), getGenericSortConditions())
                .checkSorts(sv, entry, false, services);
    }

    public SVInstantiations addInteresting(SchemaVariable sv, Name name, LogicServices services) {
        SchemaVariable existingSV = lookupVar(sv.name());
        Name oldValue = (Name) getInstantiation(existingSV);
        if (name.equals(oldValue)) {
            return this; // already have it
        } else if (oldValue != null) {
            throw new IllegalStateException(
                "Trying to add a second name proposal for " + sv + ": " + oldValue + "->" + name);
        } else {
            // otherwise (nothing here yet) add it
            return addInteresting(sv, new InstantiationEntry<>(name), services);
        }
    }

    /**
     * replaces the given pair in the instantiations. If the given SchemaVariable has been
     * instantiated already, the new pair is taken without a warning.
     *
     * @param sv the SchemaVariable to be instantiated
     * @param entry the InstantiationEntry the SchemaVariable is instantiated with
     */
    public SVInstantiations replace(SchemaVariable sv, InstantiationEntry<?> entry,
            Services services) {
        return new SVInstantiations(map.remove(sv).put(sv, entry), interesting(),
            getUpdateContext(), getGenericSortConditions()).checkSorts(sv, entry, true, services);
    }

    /**
     * adds the schemvariable to the set of interesting ones
     *
     * @throws IllegalInstantiationException, if sv has not yet been instantiated
     */
    public SVInstantiations makeInteresting(SchemaVariable sv, LogicServices services) {
        final InstantiationEntry<?> entry = getInstantiationEntry(sv);

        if (entry == null) {
            throw new IllegalInstantiationException(
                sv + " cannot be made interesting. As it is not yet in the map.");
        }

        return new SVInstantiations(map, interesting().put(sv, entry), getUpdateContext(),
            getGenericSortConditions()).checkSorts(sv, entry, true, services);

    }


    /**
     * replaces the given pair in the instantiations. If the given SchemaVariable has been
     * instantiated already, the new pair is taken without a warning.
     *
     * @param sv the SchemaVariable to be instantiated
     * @param term the Term the SchemaVariable is instantiated with
     */
    public SVInstantiations replace(SchemaVariable sv, JTerm term, Services services) {
        return replace(sv, new InstantiationEntry<>(term), services);
    }

    /**
     * replaces the given pair in the instantiations. If the given SchemaVariable has been
     * instantiated already, the new pair is taken without a warning.
     *
     * @param sv the SchemaVariable to be instantiated
     * @param pe the ProgramElement the SchemaVariable is instantiated with
     */
    public SVInstantiations replace(SchemaVariable sv, ProgramElement pe, Services services) {
        return replace(sv, new InstantiationEntry<>(pe), services);
    }

    /**
     * replaces the given pair in the instantiations. If the given SchemaVariable has been
     * instantiated already, the new pair is taken without a warning.
     *
     * @param sv the SchemaVariable to be instantiated
     * @param pes the ArrayOf<t> the SchemaVariable is instantiated with
     */
    public SVInstantiations replace(SchemaVariable sv, ImmutableArray<ProgramElement> pes,
            Services services) {
        return replace(sv, new ListInstantiation(pes, ProgramElement.class), services);
    }

    /**
     * replaces the given pair in the instantiations. If the context has been instantiated already,
     * the new pair is taken without a warning.
     *
     * @param prefix the PosInProgram describing the position of the first statement after the
     *        prefix
     * @param postfix the PosInProgram describing the position of the statement just before the
     *        postfix
     * @param activeStatementContext the ExecutionContext of the first active statement
     * @param pe the ProgramElement the context positions are related to
     */
    public SVInstantiations replace(PosInProgram prefix, PosInProgram postfix,
            ExecutionContext activeStatementContext, ProgramElement pe, Services services) {
        return replace(CONTEXTSV,
            new InstantiationEntry<>(new ContextStatementBlockInstantiation(prefix, postfix,
                activeStatementContext, pe)),
            services);
    }


    /**
     * returns true iff the sv has been instantiated already
     *
     * @return true iff the sv has been instantiated already
     */
    public boolean isInstantiated(SchemaVariable sv) {
        return map.containsKey(sv);
    }

    /**
     * returns the instantiation of the given SchemaVariable
     *
     * @return the InstantiationEntry the SchemaVariable will be instantiated with, {@code null} if
     *         no
     *         instantiation is stored
     */
    public <T> InstantiationEntry<T> getInstantiationEntry(SchemaVariable sv) {
        return (InstantiationEntry<T>) map.get(sv);
    }

    /**
     * returns the instantiation of the given SchemaVariable
     *
     * @return the Object the SchemaVariable will be instantiated with, null if no instantiation is
     *         stored
     */
    @Override
    public <T> @Nullable T getInstantiation(SchemaVariable sv) {
        final InstantiationEntry<T> entry = getInstantiationEntry(sv);
        return entry == null ? null : entry.getInstantiation();
    }

    /**
     * returns the instantiation of the given SchemaVariable as Term. If the instantiation is a
     * program element it is tried to convert it to a term otherwise an exception is thrown
     *
     * @return the Object the SchemaVariable will be instantiated with, null if no instantiation is
     *         stored
     */
    public JTerm getTermInstantiation(SchemaVariable sv, ExecutionContext ec,
            LogicServices services) {
        final Object inst = getInstantiation(sv);
        if (inst == null) {
            return null;
        } else if (inst instanceof JTerm) {
            return (JTerm) inst;
        } else if (inst instanceof ProgramElement) {
            return ((Services) services).getTypeConverter()
                    .convertToLogicElement((ProgramElement) inst, ec);
        } else {
            throw CONVERT_INSTANTIATION_EXCEPTION;
        }
    }

    /**
     * adds an update to the update context
     *
     * @param updateApplicationlabels the TermLabels attached to the application operator term
     */
    public SVInstantiations addUpdate(JTerm update,
            ImmutableArray<TermLabel> updateApplicationlabels) {
        assert update.sort() == JavaDLTheory.UPDATE;
        return new SVInstantiations(map, interesting(),
            updateContext.append(new UpdateLabelPair(update, updateApplicationlabels)),
            getGenericSortInstantiations(), getGenericSortConditions());
    }

    public record UpdateLabelPair(JTerm update, ImmutableArray<TermLabel> updateApplicationlabels) {
        @Override
        public boolean equals(Object obj) {
            if (obj instanceof UpdateLabelPair) {
                return update.equals(((UpdateLabelPair) obj).update()) && updateApplicationlabels
                        .equals(((UpdateLabelPair) obj).updateApplicationlabels());
            } else {
                return false;
            }
        }

        @Override
        public int hashCode() {
            return update.hashCode() + 13 * updateApplicationlabels.hashCode();
        }
    }

    public SVInstantiations addUpdateList(ImmutableList<UpdateLabelPair> updates) {
        if (updates.isEmpty() && updateContext.isEmpty()) {
            // avoid unnecessary creation of SVInstantiations
            return this;
        }
        return new SVInstantiations(map, interesting(), updates, getGenericSortInstantiations(),
            getGenericSortConditions());
    }


    public SVInstantiations clearUpdateContext() {
        if (updateContext.isEmpty()) {
            // avoid unnecessary creation of SVInstantiations
            return this;
        }
        return new SVInstantiations(map, interesting(), ImmutableSLList.nil(),
            getGenericSortInstantiations(), getGenericSortConditions());
    }

    /**
     * returns the instantiation entry for the context "schema variable" or null if non such exists
     */
    public ContextStatementBlockInstantiation getContextInstantiation() {
        final InstantiationEntry<?> entry = getInstantiationEntry(CONTEXTSV);
        return entry == null ? null : (ContextStatementBlockInstantiation) entry.getInstantiation();
    }

    /**
     * returns iterator of the SchemaVariables that have an instantiation
     *
     * @return the Iterator<SchemaVariable>
     */
    public Iterator<SchemaVariable> svIterator() {
        return map.keyIterator();
    }

    /**
     * returns iterator of the mapped pair {@code (SchemaVariables, InstantiationEntry)}
     *
     * @return the Iterator
     */
    public Iterator<ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>>> pairIterator() {
        return map.iterator();
    }

    /**
     * returns iterator of the mapped pair {@code (SchemaVariables, InstantiationEntry)}
     *
     * @return the Iterator
     */
    public ImmutableMap<SchemaVariable, InstantiationEntry<?>> getInstantiationMap() {
        return map;
    }

    /**
     * returns the number of SchemaVariables of which an instantiation is known
     *
     * @return int that is the number of SchemaVariables of which an instantiation is known
     */
    public int size() {
        return map.size();
    }

    /**
     * returns true iff no instantiation of SchemaVariables are known
     */
    public boolean isEmpty() {
        // the interesting map needs not to be checked
        return this == EMPTY_SVINSTANTIATIONS || (map.isEmpty() && updateContext.isEmpty()
                && genericSortConditions.isEmpty() && genericSortInstantiations.isEmpty());
    }

    /**
     * returns the update context
     *
     * @return the update context
     */
    public ImmutableList<UpdateLabelPair> getUpdateContext() {
        return updateContext;
    }

    /**
     * returns true if the given object and this one have the same mappings
     *
     * @return true if the given object and this one have the same mappings
     */
    public boolean equals(Object obj) {
        final SVInstantiations cmp;
        if (!(obj instanceof SVInstantiations)) {
            return false;
        } else {
            cmp = (SVInstantiations) obj;
        }
        if (size() != cmp.size() || !getUpdateContext().equals(cmp.getUpdateContext())) {
            return false;
        }

        final Iterator<ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>>> it =
            pairIterator();
        while (it.hasNext()) {
            final ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>> e = it.next();
            final Object inst = e.value().getInstantiation();
            assert inst != null : "Illegal null instantiation.";
            if (inst instanceof JTerm instAsTerm) {
                if (!instAsTerm.equalsModProperty(cmp.getInstantiation(e.key()),
                    IRRELEVANT_TERM_LABELS_PROPERTY)) {
                    return false;
                }
            } else if (!inst.equals(cmp.getInstantiation(e.key()))) {
                return false;
            }
        }
        return true;

    }

    public int hashCode() {
        int result = 37 * getUpdateContext().hashCode() + size();
        final Iterator<ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>>> it =
            pairIterator();
        while (it.hasNext()) {
            final ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>> e = it.next();
            if (e.value().getInstantiation() instanceof TermLabel termLabel) {
                if (!termLabel.isProofRelevant()) {
                    continue;
                }
            }
            result = 37 * result + e.value().getInstantiation().hashCode() + e.key().hashCode();
        }
        return result;
    }

    public SVInstantiations union(
            org.key_project.prover.rules.instantiation.SVInstantiations p_other,
            LogicServices services) {
        final var other = (SVInstantiations) p_other;
        ImmutableMap<SchemaVariable, InstantiationEntry<?>> result = map;

        for (ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>> entry : other.map) {
            result = result.put(entry.key(), entry.value());
        }

        ImmutableList<UpdateLabelPair> updates = ImmutableSLList.nil();

        if (other.getUpdateContext().isEmpty()) {
            updates = getUpdateContext();
        } else if (getUpdateContext().isEmpty()) {
            updates = other.getUpdateContext();
        } else if (!getUpdateContext().equals(other.getUpdateContext())) {
            Debug.fail(
                "The update context of one of" + " the instantiations has to be empty or equal.");
        } else {
            updates = other.getUpdateContext();
        }
        return new SVInstantiations(result, interesting(), updates, getGenericSortConditions())
                .rebuildSorts(services);
    }

    public ImmutableMap<SchemaVariable, InstantiationEntry<?>> interesting() {
        return interesting;
    }


    @Override
    public String toString() {
        StringBuilder result = new StringBuilder("SV Instantiations: ");
        return (result.append(map.toString())).toString();
    }

    /**
     * Add the given additional condition for the generic sort instantiations
     */
    public SVInstantiations add(GenericSortCondition p_c, LogicServices services)
            throws SortException {
        return new SVInstantiations(map, interesting(), getUpdateContext(),
            getGenericSortInstantiations(), getGenericSortConditions().prepend(p_c))
                .checkCondition(p_c, false, services);
    }

    public ExecutionContext getExecutionContext() {
        final ContextStatementBlockInstantiation cte = getContextInstantiation();
        if (cte != null) {
            return cte.activeStatementContext();
        } else {
            return null;
        }
    }

    public ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>> lookupEntryForSV(Name name) {
        for (ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>> e : map) {
            if (e.key().name().equals(name)) {
                return e;
            }
        }
        return null; // handle this better!
    }

    @Override
    public @Nullable SchemaVariable lookupVar(@NonNull Name name) {
        final var e = lookupEntryForSV(name);
        return e == null ? null : e.key(); // handle this better!
    }

    @Override
    public <T> @Nullable T lookupValue(@NonNull Name name) {
        final var e = lookupEntryForSV(name);
        // e.value() cannot be null here as null instantiations are not allowed
        return e == null ? null : (T) e.value().getInstantiation();
    }
}
