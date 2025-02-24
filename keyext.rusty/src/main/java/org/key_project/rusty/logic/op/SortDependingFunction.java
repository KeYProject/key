/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.op;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.NamespaceSet;
import org.key_project.rusty.logic.RustyDLTheory;
import org.key_project.rusty.logic.sort.GenericSort;
import org.key_project.rusty.logic.sort.ProgramSVSort;
import org.key_project.util.collection.ImmutableArray;

/**
 * The objects of this class represent families of function symbols, where each family contains an
 * instantiation of a template symbol for a particular sort. The following invariant has to hold:
 * Given two sort-depending functions {@code f1} and {@code f2} then from {@code f1.isSimilar(f2)}
 * and
 * {@code f1.getSortDependingOn() == f2.getSortDependingOn()} follows {@code f1 == f2}.
 */
public final class SortDependingFunction extends Function {
    private final SortDependingFunctionTemplate template;
    private final Qualifier<Sort> sortDependingOn;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------
    private SortDependingFunction(SortDependingFunctionTemplate template, Sort sortDependingOn) {
        super(instantiateName(template.kind, sortDependingOn),
            instantiateArgSorts(template, sortDependingOn),
            instantiateResultSort(template, sortDependingOn), null, template.unique, false, false);
        this.template = template;
        this.sortDependingOn = Qualifier.create(sortDependingOn);
    }

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    private static Name instantiateName(Name kind, Sort sortDependingOn) {
        return new Name(sortDependingOn + "::" + kind);
    }


    private static Sort instantiateResultSort(SortDependingFunctionTemplate template,
            Sort sortDependingOn) {
        return template.sort == template.sortDependingOn ? sortDependingOn : template.sort;
    }


    private static ImmutableArray<Sort> instantiateArgSorts(SortDependingFunctionTemplate template,
            Sort sortDependingOn) {
        Sort[] result = new Sort[template.argSorts.size()];
        for (int i = 0; i < result.length; i++) {
            result[i] = (template.argSorts.get(i) == template.sortDependingOn ? sortDependingOn
                    : template.argSorts.get(i));
        }
        return new ImmutableArray<>(result);
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    @Override
    public int hashCode() {
        return name().hashCode();
    }

    public static SortDependingFunction createFirstInstance(GenericSort sortDependingOn, Name kind,
            Sort sort, Sort[] argSorts, boolean unique) {
        SortDependingFunctionTemplate template = new SortDependingFunctionTemplate(sortDependingOn,
            kind, sort, new ImmutableArray<>(argSorts), unique);
        return new SortDependingFunction(template, RustyDLTheory.ANY);
    }


    public static SortDependingFunction getFirstInstance(Name kind, Services services) {
        return (SortDependingFunction) services.getNamespaces().functions()
                .lookup(instantiateName(kind, RustyDLTheory.ANY));
    }

    /**
     * returns the variant for the given sort
     *
     * @param sort the {@link Sort} for which to retrieve the corresponding variant of this function
     * @param services the {@link Services}
     * @return the variant for the given sort
     */
    public synchronized SortDependingFunction getInstanceFor(Sort sort, Services services) {
        if (sort == this.sortDependingOn.getQualifier())
            return this;

        var n = (SortDependingFunction) services.getNamespaces()
                .lookup(instantiateName(getKind(), sort));

        if (sort instanceof ProgramSVSort)
            throw new AssertionError();
        if (sort == AbstractTermTransformer.METASORT)
            throw new AssertionError();

        final NamespaceSet namespaces = services.getNamespaces();
        Namespace<Function> functions = namespaces.functions();

        SortDependingFunction result;
        synchronized (namespaces) {
            result = (SortDependingFunction) namespaces.lookup(instantiateName(getKind(), sort));
            // ugly: multiple generic sorts with the same name may exist over time

            if (result != null && sort instanceof GenericSort
                    && result.getSortDependingOn() != sort) {
                result = new SortDependingFunction(template, sort);
                synchronized (functions) {
                    functions.add(result);
                }
            } else if (result == null) {
                result = new SortDependingFunction(template, sort);
                // The namespaces may be wrapped for local symbols
                // Sort depending on functions are to be added to the "root" namespace, however.
                // Therefore, let's rewind to the root (MU, 2017-03)
                synchronized (functions) {
                    while (functions.parent() != null) {
                        functions = functions.parent();
                    }
                    synchronized (functions) {
                        functions.addSafely(result);
                    }
                }
            }
        }

        if (result.getSortDependingOn() != sort) {
            throw new AssertionError(
                String.format("%s depends on %s (hash %d) but should depend on %s (hash %d)",
                    result, result.getSortDependingOn(), result.hashCode(), sort, sort.hashCode()));
        }
        if (!isSimilar(result)) {
            throw new AssertionError(result + " should be similar to " + this);
        }
        if (namespaces.lookup(instantiateName(getKind(), sort)) != result) {
            throw new AssertionError();
        }

        return result;
    }

    public Sort getSortDependingOn() {
        return sortDependingOn.getQualifier();
    }


    public boolean isSimilar(SortDependingFunction p) {
        return getKind().equals(p.getKind());
    }


    public Name getKind() {
        return template.kind;
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    @Override
    public SyntaxElement getChild(int n) {
        if (n == 0) {
            return sortDependingOn;
        }
        throw new IndexOutOfBoundsException(
            "SortDependingFunction " + name() + " has only one child");
    }

    private record SortDependingFunctionTemplate(GenericSort sortDependingOn, Name kind, Sort sort,
            ImmutableArray<Sort> argSorts, boolean unique) {}
}
