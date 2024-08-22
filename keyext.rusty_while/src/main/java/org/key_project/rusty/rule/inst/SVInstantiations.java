/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.inst;

import java.util.Iterator;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.logic.PosInProgram;
import org.key_project.rusty.logic.RustyDLTheory;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.sv.OperatorSV;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.logic.op.sv.SchemaVariableFactory;
import org.key_project.rusty.logic.sort.ProgramSVSort;
import org.key_project.util.collection.*;

import static org.key_project.rusty.rule.match.instructions.MatchProgramSVInstruction.convertToLogicElement;

public class SVInstantiations {
    /** the empty instantiation */
    public static final SVInstantiations EMPTY_SVINSTANTIATIONS = new SVInstantiations();
    /**
     * the context itself is not realised as a schemavariable, therefore we need here a dummy SV for
     * a more unified handling (key in map)
     */
    private static final SchemaVariable CONTEXTSV = SchemaVariableFactory.createProgramSV(
        new Name("Context"), new ProgramSVSort(new Name("ContextStatementBlock")) {
            public boolean canStandFor(RustyProgramElement pe, Services services) {
                return true;
            }
        }, false); // just a dummy SV for context

    /** the map with the instantiations to logic terms */
    private final ImmutableMap<SchemaVariable, InstantiationEntry<?>> map;

    /**
     * updates may be ignored when matching, therefore they need to be added after the application
     * around the added/replaced parts. These are stored in this list
     */
    private final ImmutableList<Term> updateContext;

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
        // interesting = DefaultImmutableMap.nilMap();
    }

    /**
     * creates a new SVInstantions object using the given map
     *
     * @param map the ImmMap<SchemaVariable,InstantiationEntry<?>> with the instantiations
     */
    private SVInstantiations(ImmutableMap<SchemaVariable, InstantiationEntry<?>> map,
            // ImmutableMap<SchemaVariable, InstantiationEntry<?>> interesting,
            ImmutableList<Term> updateContext,
            GenericSortInstantiations genericSortInstantiations,
            ImmutableList<GenericSortCondition> genericSortConditions) {
        this.map = map;
        // this.interesting = interesting;
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
     * @param subst the Term the SchemaVariable is instantiated with
     * @return SVInstantiations the new SVInstantiations containing the given pair
     */
    public SVInstantiations add(SchemaVariable sv, Term subst, Services services) {
        return add(sv, new TermInstantiation(sv, subst), services);
    }

    public SVInstantiations add(SchemaVariable sv, ProgramList pes, Services services) {
        return add(sv, new ProgramListInstantiation(pes.list()), services);
    }

    /**
     * Add the given additional condition for the generic sort instantiations
     */
    public SVInstantiations add(SchemaVariable sv, Modality.RustyModalityKind kind,
            Services services) throws SortException {
        return add(sv, new InstantiationEntry<>(kind) {
        }, services);
    }

    public SVInstantiations addList(SchemaVariable sv, Object[] list, Services services) {
        return add(sv, new ListInstantiation(sv, ImmutableSLList.nil().prepend(list)),
            services);
    }

    /**
     * adds the given pair to the instantiations. If the given SchemaVariable has been instantiated
     * already, the new pair is taken without a warning.
     *
     * @param sv the SchemaVariable to be instantiated
     * @param pe the ProgramElement the SchemaVariable is instantiated with
     * @return SVInstantiations the new SVInstantiations containing the given pair
     */
    public SVInstantiations add(SchemaVariable sv, RustyProgramElement pe, Services services) {
        return add(sv, new ProgramInstantiation(pe), services);
    }

    /**
     * adds the given pair to the instantiations. If the given SchemaVariable has been instantiated
     * already, the new pair is taken without a warning.
     *
     * @param sv the SchemaVariable to be instantiated
     * @param entry the InstantiationEntry
     * @return SVInstantiations the new SVInstantiations containing the given pair
     */
    public SVInstantiations add(SchemaVariable sv, InstantiationEntry<?> entry, Services services) {
        return new SVInstantiations(map.put(sv, entry), getUpdateContext(),
            getGenericSortInstantiations(), getGenericSortConditions()).checkSorts(sv, entry, false,
                services);
    }

    /**
     * returns the update context
     *
     * @return the update context
     */
    public ImmutableList<Term> getUpdateContext() {
        return updateContext;
    }

    private static final SortException INCOMPATIBLE_INSTANTIATION_EXCEPTION =
        new SortException("Sort of SV " + "is not compatible with its " + "instantiation's sort\n"
            + "(This exception object is static)");

    private static final IllegalInstantiationException CONVERT_INSTANTIATION_EXCEPTION =
        new SortException("Instantiation of SV " + "cannot be converted to logic\n"
            + "(This exception object is static)");

    private static final SortException UNSOLVABLE_SORT_CONDITIONS_EXCEPTION = new SortException(
        "Conditions for sorts" + " cannot be satisfied\n" + "(This exception object is static)");

    private SVInstantiations checkSorts(SchemaVariable p_sv, InstantiationEntry<?> p_entry,
            boolean p_forceRebuild, Services services) {
        if (p_sv instanceof OperatorSV asv) {
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
            Services services) {
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

    private SVInstantiations rebuildSorts(Services services) {
        genericSortInstantiations =
            GenericSortInstantiations.create(map.iterator(), getGenericSortConditions(), services);
        return this;
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
    public InstantiationEntry<?> getInstantiationEntry(SchemaVariable sv) {
        return map.get(sv);
    }

    /**
     * returns the instantiation of the given SchemaVariable
     *
     * @return the Object the SchemaVariable will be instantiated with, null if no instantiation is
     *         stored
     */
    public Object getInstantiation(SchemaVariable sv) {
        final InstantiationEntry<?> entry = getInstantiationEntry(sv);
        return entry == null ? null : entry.getInstantiation();
    }

    /**
     * returns the instantiation entry for the context "schema variable" or null if non such exists
     */
    public ContextInstantiationEntry getContextInstantiation() {
        final InstantiationEntry<?> entry = getInstantiationEntry(CONTEXTSV);
        return (ContextInstantiationEntry) entry;
    }

    /**
     * returns the instantiation of the given SchemaVariable as Term. If the instantiation is a
     * program element it is tried to convert it to a term otherwise an exception is thrown
     *
     * @return the Object the SchemaVariable will be instantiated with, null if no instantiation is
     *         stored
     */
    public Term getTermInstantiation(SchemaVariable sv, Services services) {
        final Object inst = getInstantiation(sv);
        if (inst == null) {
            return null;
        } else if (inst instanceof Term) {
            return (Term) inst;
        } else if (inst instanceof RustyProgramElement pe) {
            return convertToLogicElement(pe, services);
        } else {
            throw CONVERT_INSTANTIATION_EXCEPTION;
        }
    }

    /**
     * adds an update to the update context
     */
    public SVInstantiations addUpdate(Term update) {
        assert update.sort() == RustyDLTheory.UPDATE;
        return new SVInstantiations(map,
            updateContext.append(update),
            getGenericSortInstantiations(), getGenericSortConditions());
    }

    public SVInstantiations addUpdateList(ImmutableList<Term> updates) {
        if (updates.isEmpty() && updateContext.isEmpty()) {
            // avoid unnecessary creation of SVInstantiations
            return this;
        }
        return new SVInstantiations(map, updates, getGenericSortInstantiations(),
            getGenericSortConditions());
    }

    public SVInstantiations clearUpdateContext() {
        if (updateContext.isEmpty()) {
            // avoid unnecessary creation of SVInstantiations
            return this;
        }
        return new SVInstantiations(map, ImmutableSLList.nil(),
            getGenericSortInstantiations(), getGenericSortConditions());
    }

    /// **
    // * returns the instantiation entry for the context "schema variable" or null if non such
    /// exists
    // */
    // public ContextInstantiationEntry getContextInstantiation() {
    // final InstantiationEntry<?> entry = getInstantiationEntry(CONTEXTSV);
    // return (ContextInstantiationEntry) entry;
    // }

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

    public SVInstantiations union(SVInstantiations other, Services services) {
        ImmutableMap<SchemaVariable, InstantiationEntry<?>> result = map;

        for (ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>> entry : other.map) {
            result = result.put(entry.key(), entry.value());
        }

        ImmutableList<Term> updates = getUpdates(other);
        return new SVInstantiations(result, updates, getGenericSortInstantiations(),
            getGenericSortConditions())
                    .rebuildSorts(services);
    }

    private ImmutableList<Term> getUpdates(SVInstantiations other) {
        ImmutableList<Term> updates = ImmutableSLList.nil();

        if (other.getUpdateContext().isEmpty()) {
            updates = getUpdateContext();
        } else if (getUpdateContext().isEmpty()) {
            updates = other.getUpdateContext();
        } else if (!getUpdateContext().equals(other.getUpdateContext())) {
            // Debug.fail(
            // "The update context of one of" + " the instantiations has to be empty or equal.");
        } else {
            updates = other.getUpdateContext();
        }
        return updates;
    }

    @Override
    public String toString() {
        StringBuilder result = new StringBuilder("SV Instantiations: ");
        return (result.append(map.toString())).toString();
    }

    /**
     * Add the given additional condition for the generic sort instantiations
     */
    public SVInstantiations add(GenericSortCondition p_c, Services services) throws SortException {
        return new SVInstantiations(map, getUpdateContext(),
            getGenericSortInstantiations(), getGenericSortConditions().prepend(p_c))
                    .checkCondition(p_c, false, services);
    }

    public ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>> lookupEntryForSV(Name name) {
        for (ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>> e : map) {
            if (e.key().name().equals(name)) {
                return e;
            }
        }
        return null; // handle this better!
    }

    public SchemaVariable lookupVar(Name name) {
        final ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>> e = lookupEntryForSV(name);
        return e == null ? null : e.key(); // handle this better!
    }

    public Object lookupValue(Name name) {
        final ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>> e = lookupEntryForSV(name);
        return e == null ? null : e.value().getInstantiation();
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
            if (inst instanceof Term instAsTerm) {
                if (!instAsTerm.equals(cmp.getInstantiation(e.key()))) {
                    return false;
                }
            } else if (!inst.equals(cmp.getInstantiation(e.key()))) {
                return false;
            }
        }
        return true;
    }

    /**
     * replaces the given pair in the instantiations. If the context has been instantiated already,
     * the new pair is taken without a warning.
     *
     * @param prefix the PosInProgram describing the position of the first statement after the
     *        prefix
     * @param postfix the PosInProgram describing the position of the statement just before the
     *        postfix
     * @param pe the ProgramElement the context positions are related to
     */
    public SVInstantiations replace(PosInProgram prefix, PosInProgram postfix,
            RustyProgramElement pe, Services services) {
        return replace(CONTEXTSV,
            new ContextInstantiationEntry(prefix, postfix, pe), services);
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
        return new SVInstantiations(map.remove(sv).put(sv, entry),
            getUpdateContext(), GenericSortInstantiations.EMPTY_INSTANTIATIONS,
            getGenericSortConditions()).checkSorts(sv, entry, true, services);
    }
}
