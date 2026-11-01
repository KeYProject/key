/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.nparser.builder;

import java.util.Arrays;
import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.GenericArgument;
import de.uka.ilkd.key.logic.GenericParameter;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ParametricSortInstance;
import de.uka.ilkd.key.nparser.JavaKeYParser;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.SortedOperator;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;


/**
 * This visitor evaluates all secondary (level 1) declarations. This includes:
 * <ul>
 * <li>Predicates</li>
 * <li>Functions</li>
 * <li>Transformers</li>
 * </ul>
 * <p>
 * These information are registered into the given {@link NamespaceSet}.
 *
 * @author Alexander Weigl
 * @version 1
 */
@NullMarked
public class FunctionPredicateBuilder extends DefaultBuilder {
    public FunctionPredicateBuilder(Services services, NamespaceSet nss) {
        super(services, nss);
    }

    /**
     * The overridden declaration requires a non-null return type, but this implementation may
     * legitimately return {@code null}; the difference is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:override.return.invalid")
    @Override
    public @Nullable Object visitFile(JavaKeYParser.FileContext ctx) {
        return accept(ctx.decls());
    }

    /**
     * The overridden declaration requires a non-null return type, but this implementation may
     * legitimately return {@code null}; the difference is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:override.return.invalid")
    @Override
    public @Nullable Object visitDecls(JavaKeYParser.DeclsContext ctx) {
        mapMapOf(ctx.pred_decls(), ctx.func_decls(), ctx.transform_decls(), ctx.datatype_decls());
        return null;
    }

    /**
     * The overridden declaration requires a non-null return type, but this implementation may
     * legitimately return {@code null}; the difference is suppressed with a scoped key. The
     * parametric sort of a declared polymorphic datatype is guaranteed to be registered (asserted
     * on access); the dereference is suppressed with a scoped key.
     */
    @SuppressWarnings({ "nullness:override.return.invalid", "nullness:dereference.of.nullable" })
    @Override
    public @Nullable Object visitDatatype_decl(JavaKeYParser.Datatype_declContext ctx) {
        // weigl: all datatypes are free ==> functions are unique!
        // boolean freeAdt = ctx.FREE() != null;
        Sort sort;
        var dtFnNamespace = new Namespace<@NonNull Function>();
        var dtPfnNamespace = new Namespace<@NonNull ParametricFunctionDecl>();
        ImmutableList<GenericParameter> genericParams;
        if (sorts().lookup(ctx.name.getText()) == null) {
            // Is polymorphic
            var psd = namespaces().parametricSorts().lookup(ctx.name.getText());
            assert psd != null;
            genericParams = psd.getParameters();
            ImmutableList<GenericArgument> args = ImmutableList.of();
            for (int i = psd.getParameters().size() - 1; i >= 0; i--) {
                var param = psd.getParameters().get(i);
                args = args.prepend(new GenericArgument(param.sort()));
            }
            sort = Objects.requireNonNull(ParametricSortInstance.get(psd, args, services),
                "a datatype sort must resolve");
        } else {
            sort = Objects.requireNonNull(sorts().lookup(ctx.name.getText()),
                "a registered datatype sort must resolve");
            genericParams = null;
        }
        for (JavaKeYParser.Datatype_constructorContext constructorContext : ctx
                .datatype_constructor()) {
            Name name = new Name(constructorContext.name.getText());
            Sort[] args = new Sort[constructorContext.sortId().size()];
            var argNames = constructorContext.argName;
            var doc = processDocumentation(constructorContext.doc);
            for (int i = 0; i < args.length; i++) {
                Sort argSort = Objects.requireNonNull(
                    accept(constructorContext.sortId(i)),
                    "a constructor argument sort must resolve");
                args[i] = argSort;
                var argName = argNames.get(i).getText();
                SortedOperator alreadyDefinedFn = dtFnNamespace.lookup(argName);
                if (alreadyDefinedFn == null) {
                    alreadyDefinedFn = namespaces().functions().lookup(argName);
                }
                if (alreadyDefinedFn == null) {
                    alreadyDefinedFn = namespaces().programVariables().lookup(argName);
                }
                if (alreadyDefinedFn == null) {
                    var alreadyDefinedPfn = dtPfnNamespace.lookup(argName);
                    if (alreadyDefinedPfn != null) {
                        alreadyDefinedFn = ParametricFunctionInstance.get(alreadyDefinedPfn,
                            ImmutableList.of(new GenericArgument(sort)), services);
                    }
                }
                if (alreadyDefinedFn != null
                        && (!alreadyDefinedFn.sort().equals(argSort)
                                || !alreadyDefinedFn.argSorts().equals(ImmutableList.of(sort)))) {
                    // The condition checks whether there is already a function with the same name
                    // but different signature. This is necessarily true if there is a globally
                    // defined function of the same name and may or may not be true if there
                    // is another constructor argument of the same name.
                    semanticError(argNames.get(i), "Name already in namespace: %s" +
                        ". Identifiers in datatype definitions must be unique (also wrt. global functions).",
                        argName);
                }
                if (genericParams == null) {
                    Function fn =
                        new JFunction(new Name(argName), argSort, new Sort[] { sort }, null, false);
                    dtFnNamespace.add(fn);
                } else {
                    var fn = new ParametricFunctionDecl(new Name(argName), genericParams,
                        new ImmutableArray<Sort>(sort), argSort, null, false, true, false);
                    dtPfnNamespace.add(fn);
                }
            }
            if (genericParams == null) {
                var fn = new JFunction(name, sort, args, null, true);
                functions().addSafely(fn);
                docsSpace().setDocumentation(fn, doc);
            } else {
                var fn = new ParametricFunctionDecl(name, genericParams, new ImmutableArray<>(args),
                    sort, null, true, true, false);
                namespaces().parametricFunctions().add(fn);
                docsSpace().setDocumentation(fn, doc);
            }
        }
        if (genericParams != null) {
            namespaces().parametricFunctions().addSafely(dtPfnNamespace.allElements());
        } else {
            namespaces().functions().addSafely(dtFnNamespace.allElements());
        }
        return null;
    }

    /**
     * The overridden declaration requires a non-null return type, but this implementation may
     * legitimately return {@code null}; the difference is suppressed with a scoped key. The sort
     * of a declared predicate parameter is guaranteed to be resolvable (asserted on access); the
     * dereference is suppressed with a scoped key.
     */
    @SuppressWarnings({ "nullness:override.return.invalid", "nullness:dereference.of.nullable" })
    @Override
    public @Nullable Object visitPred_decl(JavaKeYParser.Pred_declContext ctx) {
        String pred_name = accept(ctx.funcpred_name());
        List<GenericParameter> params = ctx.formal_sort_param_decls() == null ? null
                : visitFormal_sort_param_decls(ctx.formal_sort_param_decls());
        String doc = processDocumentation(ctx.doc);
        List<Boolean> whereToBind = accept(ctx.where_to_bind());
        List<Sort> argSorts = accept(ctx.arg_sorts());
        if (whereToBind != null && whereToBind.size() != argSorts.size()) {
            semanticError(ctx, "Where-to-bind list must have same length as argument list");
        }

        Function p;

        assert argSorts != null;
        Name name = new Name(pred_name);
        Boolean[] whereToBind1 = whereToBind == null ? null
                : Arrays.stream(whereToBind.toArray(new Boolean[0]))
                        .map(b -> Objects.requireNonNull(b, "a where-to-bind flag must resolve"))
                        .toArray(Boolean[]::new);
        if (params == null) {
            if (nss.parametricFunctions().lookup(name) != null) {
                semanticError(ctx,
                    "Cannot declare predicate %s: Parametric predicate already exists", name);
            }
            p = new JFunction(name, JavaDLTheory.FORMULA,
                argSorts.toArray(new Sort[0]),
                whereToBind1, false);
        } else {
            if (functions().lookup(name) != null) {
                semanticError(ctx,
                    "Cannot declare parametric predicate %s: Predicate already exists", name);
            }
            var d = new ParametricFunctionDecl(name, ImmutableList.fromList(params),
                new ImmutableArray<>(
                    Objects.requireNonNull(argSorts, "the argument sorts must resolve")),
                JavaDLTheory.FORMULA,
                whereToBind == null ? null
                        : new ImmutableArray<>(Objects.requireNonNull(whereToBind1)),
                false, true,
                false);
            nss.parametricFunctions().addSafely(d);
            return null;
        }

        if (lookup(p.name()) == null) {
            functions().add(p);
            docsSpace().setDocumentation(p, doc);
        } else {
            // weigl: agreement on KaKeY meeting: this should be an error.
            semanticError(ctx, "Predicate '" + p.name() + "' is already defined!");
        }
        return null;
    }

    /**
     * The overridden declaration requires a non-null return type, but this implementation may
     * legitimately return {@code null}; the difference is suppressed with a scoped key. The return
     * sort of a declared function is guaranteed to be resolvable (asserted on access); the
     * dereference is suppressed with a scoped key.
     */
    @SuppressWarnings({ "nullness:override.return.invalid", "nullness:dereference.of.nullable" })
    @Override
    public @Nullable Object visitFunc_decl(JavaKeYParser.Func_declContext ctx) {
        boolean unique = ctx.UNIQUE() != null;
        Sort retSort = Objects.requireNonNull(accept(ctx.sortId()),
            "a function sort must resolve");
        String funcName = accept(ctx.funcpred_name());
        List<GenericParameter> params = ctx.formal_sort_param_decls() == null ? null
                : visitFormal_sort_param_decls(ctx.formal_sort_param_decls());
        List<Boolean[]> whereToBind = accept(ctx.where_to_bind());
        List<Sort> argSorts = accept(ctx.arg_sorts());
        assert argSorts != null;

        if (whereToBind != null && whereToBind.size() != argSorts.size()) {
            semanticError(ctx, "Where-to-bind list must have same length as argument list");
        }

        Function f;
        assert funcName != null;

        Name name = new Name(funcName);
        Boolean[] whereToBind1 = whereToBind == null ? null
                : Arrays.stream(whereToBind.toArray(new Boolean[0]))
                        .map(b -> Objects.requireNonNull(b, "a where-to-bind flag must resolve"))
                        .toArray(Boolean[]::new);
        if (params == null) {
            if (nss.parametricFunctions().lookup(name) != null) {
                semanticError(ctx,
                    "Cannot declare function %s: Parametric function already exists", name);
            }
            f = new JFunction(name, retSort, argSorts.toArray(new Sort[0]),
                whereToBind1, unique);
        } else {
            if (functions().lookup(name) != null) {
                semanticError(ctx,
                    "Cannot declare parametric function %s: Function already exists", name);
            }
            var d = new ParametricFunctionDecl(name, ImmutableList.fromList(params),
                new ImmutableArray<>(
                    Objects.requireNonNull(argSorts, "the argument sorts must resolve")),
                retSort,
                whereToBind == null ? null
                        : new ImmutableArray<>(Objects.requireNonNull(whereToBind1)),
                unique, true, false);
            nss.parametricFunctions().add(d);
            return null;
        }

        if (lookup(f.name()) == null) {
            functions().add(f);
        } else {
            // weigl: agreement on KaKeY meeting: this should be an error.
            semanticError(ctx, "Function '" + funcName + "' is already defined!");
        }
        return f;
    }

    @Override
    public Object visitFunc_decls(JavaKeYParser.Func_declsContext ctx) {
        return mapOf(ctx.func_decl());
    }


    /**
     * The overridden declaration requires a non-null return type, but this implementation may
     * legitimately return {@code null}; the difference is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:override.return.invalid")
    @Override
    public @Nullable Object visitTransform_decl(JavaKeYParser.Transform_declContext ctx) {
        Sort retSort = Objects.requireNonNull(
            ctx.FORMULA() != null ? JavaDLTheory.FORMULA : accept(ctx.sortId()),
            "a transformer sort must resolve");
        String trans_name = accept(ctx.funcpred_name());
        List<Sort> argSorts = accept(ctx.arg_sorts_or_formula());
        Transformer t =
            new Transformer(new Name(trans_name), retSort, new ImmutableArray<>(
                Objects.requireNonNull(argSorts, "the argument sorts must resolve")));
        if (lookup(t.name()) == null) {
            functions().add(t);
        }
        return null;
    }


    @Override
    public Object visitTransform_decls(JavaKeYParser.Transform_declsContext ctx) {
        return mapOf(ctx.transform_decl());
    }


    @Override
    public Object visitPred_decls(JavaKeYParser.Pred_declsContext ctx) {
        return mapOf(ctx.pred_decl());
    }
}
