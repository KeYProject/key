/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;


import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ParametricFunctionDecl;
import de.uka.ilkd.key.logic.sort.ParametricSortDecl;
import de.uka.ilkd.key.logic.sort.SortAlias;

import org.key_project.logic.Choice;
import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.RuleSet;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;


@NullMarked
public class NamespaceSet {
    private final Map<Class<?>, Namespace<?>> namespaces = new HashMap<>();

    /*
     * private Namespace<QuantifiableVariable> varNS = new Namespace<>();
     * private Namespace<IProgramVariable> progVarNS = new Namespace<>();
     * // TODO: Operators should not be local to goals
     * private Namespace<Function> funcNS = new Namespace<>();
     * private Namespace<RuleSet> ruleSetNS = new Namespace<>();
     * private Namespace<Sort> sortNS = new Namespace<>();
     * private Namespace<SortAlias> sortAliases = new Namespace<>();
     * private Namespace<ParametricSortDecl> parametricSortNS = new Namespace<>();
     * private Namespace<ParametricFunctionDecl> parametricFuncNS = new Namespace<>();
     * private Namespace<Choice> choiceNS = new Namespace<>();
     */
    private org.key_project.logic.MetaSpace documentation = new org.key_project.logic.MetaSpace();

    public NamespaceSet() {
    }

    public NamespaceSet(Map<Class<?>, Namespace<?>> namespaces,
            org.key_project.logic.MetaSpace documentation) {
        this.documentation = documentation;
        this.namespaces.putAll(namespaces);
    }

    @Deprecated
    public NamespaceSet(Namespace<QuantifiableVariable> varNS,
            Namespace<Function> funcNS,
            Namespace<Sort> sortNS,
            Namespace<SortAlias> sortAliases,
            Namespace<RuleSet> ruleSetNS,
            Namespace<ParametricSortDecl> parametricSortNS,
            Namespace<ParametricFunctionDecl> parametricFuncNS,
            Namespace<Choice> choiceNS,
            Namespace<IProgramVariable> programVarNS) {
        this(varNS, funcNS, sortNS, sortAliases, ruleSetNS,
            parametricSortNS, parametricFuncNS,
            choiceNS, programVarNS, new org.key_project.logic.MetaSpace());
    }

    @Deprecated
    public NamespaceSet(Namespace<QuantifiableVariable> varNS,
            Namespace<Function> funcNS,
            Namespace<Sort> sortNS,
            Namespace<SortAlias> sortAliases,
            Namespace<RuleSet> ruleSetNS,
            Namespace<ParametricSortDecl> parametricSortNS,
            Namespace<ParametricFunctionDecl> parametricFuncNS,
            Namespace<Choice> choiceNS,
            Namespace<IProgramVariable> programVarNS,
            org.key_project.logic.MetaSpace documentation) {
        register(QuantifiableVariable.class, varNS);
        register(IProgramVariable.class, programVarNS);
        register(Function.class, funcNS);
        register(Sort.class, sortNS);
        register(SortAlias.class, sortAliases);
        register(RuleSet.class, ruleSetNS);
        register(Choice.class, choiceNS);
        register(ParametricSortDecl.class, parametricSortNS);
        register(ParametricFunctionDecl.class, parametricFuncNS);
        this.documentation = documentation;
    }

    private <T extends Named> void register(Class<T> clazz, Namespace<T> ns) {
        namespaces.put(clazz, ns);
    }

    @SuppressWarnings("unchecked")
    private <T extends Named> Namespace<T> get(Class<T> key) {
        return (Namespace<T>) namespaces.computeIfAbsent(key, (it) -> new Namespace<>());
    }


    public NamespaceSet copy() {
        var namespaces = new HashMap<Class<?>, Namespace<?>>();
        this.namespaces.forEach((k, v) -> namespaces.put(k, v.copy()));
        return new NamespaceSet(namespaces, documentation.copy());
    }

    public NamespaceSet shallowCopy() {
        return new NamespaceSet(namespaces, new org.key_project.logic.MetaSpace(documentation));
    }

    // TODO MU: Rename into sth with wrap or similar
    public NamespaceSet copyWithParent() {
        var namespaces = new HashMap<Class<?>, Namespace<?>>();
        this.namespaces.forEach((k, v) -> namespaces.put(k, new Namespace<>(v)));
        return new NamespaceSet(namespaces, new org.key_project.logic.MetaSpace(documentation));
    }

    public Namespace<QuantifiableVariable> variables() {
        return get(QuantifiableVariable.class);
    }

    public void setVariables(Namespace<QuantifiableVariable> varNS) {
        register(QuantifiableVariable.class, varNS);
    }

    public Namespace<IProgramVariable> programVariables() {
        return get(IProgramVariable.class);
    }

    public void setProgramVariables(Namespace<IProgramVariable> progVarNS) {
        register(IProgramVariable.class, progVarNS);
    }

    public Namespace<Function> functions() {
        return get(Function.class);
    }

    public void setFunctions(Namespace<Function> funcNS) {
        register(Function.class, funcNS);
    }

    public Namespace<RuleSet> ruleSets() {
        return get(RuleSet.class);
    }

    public void setRuleSets(Namespace<RuleSet> ruleSetNS) {
        register(RuleSet.class, ruleSetNS);
    }

    public Namespace<Sort> sorts() {
        return get(Sort.class);
    }

    public void setSorts(Namespace<Sort> sortNS) {
        register(Sort.class, sortNS);
    }

    public Namespace<SortAlias> sortAliases() {
        return get(SortAlias.class);
    }

    public void setSortAliases(Namespace<SortAlias> sortAliases) {
        register(SortAlias.class, sortAliases);
    }

    public Namespace<ParametricSortDecl> parametricSorts() {
        return get(ParametricSortDecl.class);
    }

    public void setParametricSorts(Namespace<ParametricSortDecl> parametricSortNS) {
        register(ParametricSortDecl.class, parametricSortNS);
    }

    public Namespace<ParametricFunctionDecl> parametricFunctions() {
        return get(ParametricFunctionDecl.class);
    }

    public void setParametricFunctions(Namespace<ParametricFunctionDecl> parametricFuncNS) {
        register(ParametricFunctionDecl.class, parametricFuncNS);
    }

    public Namespace<Choice> choices() {
        return get(Choice.class);
    }

    public void setChoices(Namespace<Choice> choiceNS) {
        register(Choice.class, choiceNS);
    }

    public void add(NamespaceSet ns) {
        variables().add(ns.variables());
        programVariables().add(ns.programVariables());
        sorts().add(ns.sorts());
        sortAliases().add(ns.sortAliases());
        parametricFunctions().add(ns.parametricFunctions());
        parametricSorts().add(ns.parametricSorts());
        ruleSets().add(ns.ruleSets());
        functions().add(ns.functions());
        choices().add(ns.choices());
    }

    /**
     * returns all namespaces in an array
     */
    private Collection<Namespace<?>> asArray() {
        return namespaces.values();
    }

    /**
     * returns all namespaces with symbols that may occur in a real sequent (this means all
     * namespaces without variables, choices and ruleSets)
     */
    private Collection<Namespace<?>> logicAsArray() {
        return namespaces.values();
    }

    /**
     * looks up if the given name is found in one of the namespaces and returns the named object or
     * null if no object with the same name has been found
     */
    public @Nullable Named lookup(Name name) {
        return lookup(name, asArray());
    }

    /**
     * looks up for the symbol in the namespaces sort, functions and programVariables
     *
     * @param name the Name to look up
     * @return the element of the given name or null
     */
    public @Nullable Named lookupLogicSymbol(Name name) {
        return lookup(name, logicAsArray());
    }

    /**
     * retrieves an object of the given name from the namespaces; the first object found in order of
     * the
     * specified namespaces
     *
     * @param name the Name to look up
     * @param spaces the Namespaces where to look for an object of the given name
     * @return the first element with the given name if found in the given namespaces, otherwise
     *         <tt>null</tt>
     */
    private @Nullable Named lookup(Name name, Collection<Namespace<?>> spaces) {
        for (Namespace<?> space : spaces) {
            final Named n = space.lookup(name);
            if (n != null) {
                return n;
            }
        }
        return null;
    }

    public @Nullable Sort lookupSortOrAlias(String name) {
        return lookupSortOrAlias(new Name(name));
    }

    public @Nullable Sort lookupSortOrAlias(Name name) {
        var sort = sorts().lookup(name);
        if (sort != null)
            return sort;
        SortAlias alias = sortAliases().lookup(name);
        if (alias != null)
            return alias.aliasedSort();
        return null;
    }

    @Override
    public String toString() {
        return "Sorts: " + sorts() + "\n" + "Alias sorts: " + sortAliases() + "\n"
            + "Parametric sorts: " + parametricSorts() + "\n" + "Functions: " + functions() + "\n"
            + "Parametric functions: " + parametricFunctions() + "\n" + "Variables: "
            + variables() + "\n" + "ProgramVariables: " + programVariables() + "\n" + "Heuristics: "
            + ruleSets() + "\n" + "Taclet Options: " + choices() + "\n";
    }


    public <T extends Name> boolean containsAll(Iterable<T> names) {
        for (Name name : names) {
            if (lookupLogicSymbol(name) == null) {
                return false;
            }
        }
        return true;
    }

    public void seal() {
        namespaces.forEach((a, b) -> b.seal());
    }

    public boolean isEmpty() {
        return namespaces.values().stream().allMatch(it -> it.isEmpty());
    }


    // create a namespace
    public NamespaceSet simplify() {
        var newSpaces = new HashMap<>(namespaces);
        namespaces.forEach((a, b) -> newSpaces.put(a, b.simplify()));
        return new NamespaceSet(newSpaces, documentation);
    }

    public NamespaceSet getCompression() {
        var newSpaces = new HashMap<>(namespaces);
        namespaces.forEach((a, b) -> newSpaces.put(a, b.compress()));
        return new NamespaceSet(newSpaces, documentation);
    }

    public void flushToParent() {
        for (Namespace<?> ns : asArray()) {
            ns.flushToParent();
        }
    }

    public NamespaceSet getParent() {
        var newSpaces = new HashMap<Class<?>, Namespace<?>>();
        // a namespace without an enclosing layer has no parent; represent that as an empty
        // namespace rather than a null map value, so the "no null values" invariant the other
        // map operations (copy, copyWithParent, getCompression) rely on keeps holding
        namespaces.forEach((a, b) -> {
            Namespace<?> parent = b.parent();
            newSpaces.put(a, parent != null ? parent : new Namespace<>());
        });
        return new NamespaceSet(newSpaces, documentation.parent());
    }

    public org.key_project.logic.MetaSpace docs() {
        return documentation;
    }
}
