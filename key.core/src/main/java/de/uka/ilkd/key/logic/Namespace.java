/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import javax.annotation.Nullable;

import org.key_project.util.collection.ImmutableSet;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * A Namespace keeps track of already used {@link Name}s and the objects carrying these names. These
 * objects have to implement the interface {@link Named}. It is possible to have nested namespaces
 * in order to represent different visibility scopes.
 */
public class Namespace<E extends Named> implements java.io.Serializable {

    private static final long serialVersionUID = 7510655524858729144L;
    private static final Logger LOGGER = LoggerFactory.getLogger(Namespace.class);

    /**
     * The fall-back namespace for symbols not present in this Namespace.
     */
    private Namespace<E> parent;

    /**
     * The map that maps a name to a symbols of that name if it is defined in this Namespace.
     */
    private Map<Name, E> symbols;

    /**
     * A namespace can be made immutable, this is called "sealing". This flag indicates whether this
     * namespace has been sealed or not.
     */
    private boolean sealed;

    /**
     * Construct an empty Namespace without a parent namespace.
     */
    public Namespace() {
        this.parent = null;
    }

    /**
     * Construct a Namespace that uses <code>parent</code> as a fallback for finding symbols not
     * defined in this one.
     */
    public Namespace(Namespace<E> parent) {
        this.parent = parent;
    }

    /**
     * Adds the object <code>sym</code> to this Namespace. If an object with the same name is
     * already there, it is quietly replaced by <code>sym</code>. Use addSafely() instead if
     * possible.
     *
     * TODO:The problem of saving to localSym, symbols, and symbolRefs is not solved yet. (This is
     * no longer self-explanatory. mu 2016)
     *
     * If the local table is empty, then the new symbol is added as "singleton map". This has been
     * adapted from an earlier implementation, done for memory efficiency reasons: Many namespaces
     * only contain a single element; no need to allocate a hash map. The hash map is only created
     * when the 2nd element is added.
     *
     * This is not threadsafe.
     */
    public void add(E sym) {

        if (sealed) {
            LOGGER.warn("Namespace is SEALED");
            throw new IllegalStateException(
                "This namespace has been sealed; addition is not possible.");
        }

        /*
         * TODO ulbrich: Investigate in a future version Named old = lookup(sym.name()); if(old !=
         * null && old != sym) { LOGGER.warn("Clash! Name already used: " + sym.name().toString());
         * }
         */

        if (symbols == null) {
            symbols = Collections.singletonMap(sym.name(), sym);
        } else {
            if (symbols.size() == 1) {
                symbols = new LinkedHashMap<>(symbols);
            }
            symbols.put(sym.name(), sym);
        }

    }

    public void add(Namespace<E> source) {
        add(source.elements());
    }

    public void add(Iterable<? extends E> list) {
        for (E element : list) {
            add(element);
        }
    }

    /**
     * Adds the object <code>sym</code> to this namespace. Throws a runtime exception if an object
     * with the same name is already there.
     */
    public void addSafely(E sym) {
        Named old = lookup(sym.name());
        if (old != null && old != sym) {
            throw new RuntimeException("Name already in namespace: " + sym.name());
        }

        add(sym);
    }

    public void addSafely(Iterable<? extends E> names) {
        for (E name : names) {
            addSafely(name);
        }
    }

    /**
     * Remove a name from the namespace.
     *
     * Removal is not delegated to the parent namespace.
     *
     * @param name non-null name whose symbol is to be removed.
     */
    public void remove(Name name) {
        if (symbols != null) {
            symbols.remove(name);
        }
    }

    protected E lookupLocally(Name name) {
        if (symbols != null) {
            return symbols.get(name);
        } else {
            return null;
        }
    }


    /**
     * creates a new Namespace that has this as parent, and contains an entry for <code>sym</code>.
     *
     * @return the new Namespace
     */
    public Namespace<E> extended(E sym) {
        return extended(Collections.singleton(sym));
    }

    public Namespace<E> extended(Iterable<? extends E> ext) {
        Namespace<E> result = new Namespace<>(this);
        result.add(ext);
        return result;
    }

    /**
     * looks if a registered object is declared in this namespace, if negative it asks its parent
     *
     * @param name a Name representing the name of the symbol to look for
     * @return Object with name "name" or null if no such an object has been found
     */
    public @Nullable E lookup(Name name) {
        E symbol = lookupLocally(name);
        if (symbol != null) {
            return symbol;
        }

        if (parent != null) {
            return parent.lookup(name);
        }

        return null;
    }

    /** Convenience method to look up. */
    public E lookup(String name) {
        return lookup(new Name(name));
    }

    /**
     * returns list of the elements (not the keys) in this namespace (not about the one of the
     * parent)
     *
     * @return the list of the named objects
     */
    public Collection<E> elements() {
        if (symbols == null) {
            return Collections.emptyList();
        } else {
            return Collections.unmodifiableCollection(symbols.values());
        }
    }


    public Collection<E> allElements() {
        if (parent == null) {
            return new ArrayList<>(elements());
        } else {
            Collection<E> result = parent().allElements();
            result.addAll(elements());
            return result;
        }
    }

    /**
     * returns the fall-back Namespace of this Namespace, i.e. the one where symbols are looked up
     * that are not found in this one.
     */
    public Namespace<E> parent() {
        return parent;
    }

    public String toString() {
        String res = "Namespace: [local:" + symbols;
        if (parent != null) {
            res = res + "; parent:" + parent;
        }
        return res + "]";
    }

    public Namespace<E> copy() {
        Namespace<E> copy = new Namespace<>(parent);
        if (symbols != null) {
            copy.add(symbols.values());
        }

        return copy;
    }

    private void reset() {
        parent = null;
        symbols = null;
    }

    public <T extends E> void set(ImmutableSet<T> names) {
        reset();
        addSafely(names);
    }

    public void seal() {
        sealed = true;
    }

    public boolean isEmpty() {
        return symbols == null || symbols.isEmpty();
    }

    public boolean isSealed() {
        return sealed;
    }

    public Namespace<E> simplify() {
        if (parent != null && isSealed() && isEmpty()) {
            return parent;
        } else {
            return this;
        }
    }

    public Namespace<E> compress() {
        // TODO the order may be changed! This seems rather inefficient ...
        Namespace<E> result = new Namespace<>();
        result.add(allElements());
        return result;
    }

    public boolean contains(E var) {
        return lookup(var.name()) == var;
    }

    public void flushToParent() {
        if (parent == null) {
            return;
        }

        for (E element : elements()) {
            parent.add(element);
        }
        // all symbols are contained in parent now ... we are empty again.
        symbols = null;
    }

}
