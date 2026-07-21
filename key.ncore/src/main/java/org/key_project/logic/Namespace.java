/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic;

import java.util.*;
import java.util.concurrent.ConcurrentHashMap;

import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/// A Namespace keeps track of already used [Name]s and the objects carrying these names. These
/// objects have to implement the interface [Named]. It is possible to have nested namespaces
/// in order to represent different visibility scopes.
public class Namespace<E extends Named> {
    private static final Logger LOGGER = LoggerFactory.getLogger(Namespace.class);

    /// The fall-back namespace for symbols not present in this Namespace.
    private @Nullable Namespace<E> parent;

    /// The map that maps a name to a symbols of that name if it is defined in this Namespace.
    ///
    /// `volatile`, and a [ConcurrentHashMap] once it grows past the single-element optimization, so
    /// that a shared proof namespace can be read lock-free while the parallel prover concurrently
    /// interns a new parametric sort into it (see [ParametricSortInstance] -- the only writer on
    /// the
    /// proving path). Reads therefore never observe a half-mutated map. The concurrent write is an
    /// in-place `put` on the already-grown map; the singleton -> map transition only ever runs
    /// single-threaded at load time (a shared namespace already holds many symbols before proving
    /// begins), so no lock is needed. Iteration order is not consumed anywhere -- the
    /// sort-hierarchy
    /// scans and symbol collections are order-independent and no proof saver iterates namespaces --
    /// so dropping the former [LinkedHashMap] insertion order is proof-preserving.
    private volatile @Nullable Map<Name, E> symbols;

    /// A namespace can be made immutable, this is called "sealing". This flag indicates whether
    /// this
    /// namespace has been sealed or not.
    private boolean sealed;

    /// Construct an empty Namespace without a parent namespace.
    public Namespace() {
        this(null);
    }

    /// Construct a Namespace that uses <code>parent</code> as a fallback for finding symbols not
    /// defined in this one.
    public Namespace(@Nullable Namespace<E> parent) {
        this.parent = parent;
    }

    /// Adds the object <code>sym</code> to this Namespace. If an object with the same name is
    /// already there, it is quietly replaced by <code>sym</code>. Use addSafely() instead if
    /// possible.
    ///
    /// TODO:The problem of saving to localSym, symbols, and symbolRefs is not solved yet. (This is
    /// no longer self-explanatory. mu 2016)
    ///
    /// If the local table is empty, then the new symbol is added as "singleton map". This has been
    /// adapted from an earlier implementation, done for memory efficiency reasons: Many namespaces
    /// only contain a single element; no need to allocate a hash map. The hash map is only created
    /// when the 2nd element is added.
    ///
    /// A `put` into an already-grown map is thread-safe (concurrent map) and safe against
    /// concurrent
    /// readers; only the singleton/empty -> map transition must not run concurrently (it does not
    /// --
    /// see the [#symbols] field doc), so it needs no lock.
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
        } else if (symbols.size() == 1) {
            // Grow out of the immutable single-element map into a concurrent map, publishing it via
            // the volatile field so a concurrent reader sees either the old map or the full new
            // one.
            // This transition runs only single-threaded at load time (see the symbols field doc).
            Map<Name, E> grown = new ConcurrentHashMap<>();
            grown.putAll(symbols);
            grown.put(sym.name(), sym);
            symbols = grown;
        } else {
            // Already a ConcurrentHashMap: put in place -- thread-safe and allocation-free, so the
            // hot load path and the rare concurrent parametric-sort write both avoid a copy.
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

    /// Adds the object <code>sym</code> to this namespace. Throws a runtime exception if an object
    /// with the same name is already there.
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

    /// Remove a name from the namespace.
    ///
    /// Removal is not delegated to the parent namespace.
    ///
    /// @param name non-null name whose symbol is to be removed.
    public void remove(Name name) {
        if (symbols != null) {
            symbols.remove(name);
        }
    }

    protected @Nullable E lookupLocally(Name name) {
        if (symbols != null) {
            return symbols.get(name);
        } else {
            return null;
        }
    }


    /// creates a new Namespace that has this as parent, and contains an entry for <code>sym</code>.
    ///
    /// @return the new Namespace
    public Namespace<E> extended(E sym) {
        return extended(Collections.singleton(sym));
    }

    public Namespace<E> extended(Iterable<? extends E> ext) {
        Namespace<E> result = new Namespace<>(this);
        result.add(ext);
        return result;
    }

    /// looks if a registered object is declared in this namespace, if negative it asks its parent
    ///
    /// @param name a Name representing the name of the symbol to look for
    /// @return Object with name "name" or null if no such an object has been found
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

    /// Convenience method to look up.
    public @Nullable E lookup(String name) {
        return lookup(new Name(name));
    }

    /// returns list of the elements (not the keys) in this namespace (not about the one of the
    /// parent)
    ///
    /// @return the list of the named objects
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
            Collection<E> result = parent.allElements();
            result.addAll(elements());
            return result;
        }
    }

    /// returns the fall-back Namespace of this Namespace, i.e. the one where symbols are looked up
    /// that are not found in this one.
    public @Nullable Namespace<E> parent() {
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
        if (isSealed() && isEmpty() && parent != null) {
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

        var parent = this.parent;

        for (E element : elements()) {
            parent.add(element);
        }
        // all symbols are contained in parent now ... we are empty again.
        symbols = null;
    }

}
