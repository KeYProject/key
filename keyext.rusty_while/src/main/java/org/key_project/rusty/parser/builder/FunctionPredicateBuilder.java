/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.builder;

import java.util.List;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.NamespaceSet;
import org.key_project.rusty.logic.RustyDLTheory;
import org.key_project.rusty.logic.op.RFunction;
import org.key_project.rusty.parser.KeYRustyParser;

public class FunctionPredicateBuilder extends DefaultBuilder {
    public FunctionPredicateBuilder(Services services, NamespaceSet nss) {
        super(services, nss);
    }

    @Override
    public Object visitFile(KeYRustyParser.FileContext ctx) {
        return accept(ctx.decls());
    }

    @Override
    public Object visitDecls(KeYRustyParser.DeclsContext ctx) {
        mapMapOf(ctx.pred_decls(), ctx.func_decls(), ctx.transform_decls(), ctx.datatype_decls());
        return null;
    }

    @Override
    public Object visitDatatype_decl(KeYRustyParser.Datatype_declContext ctx) {
        // weigl: all datatypes are free ==> functions are unique!
        // boolean freeAdt = ctx.FREE() != null;
        var sort = sorts().lookup(ctx.name.getText());
        var dtNamespace = new Namespace<Function>();
        for (KeYRustyParser.Datatype_constructorContext constructorContext : ctx
                .datatype_constructor()) {
            Name name = new Name(constructorContext.name.getText());
            Sort[] args = new Sort[constructorContext.sortId().size()];
            var argNames = constructorContext.argName;
            for (int i = 0; i < args.length; i++) {
                Sort argSort = accept(constructorContext.sortId(i));
                args[i] = argSort;
                var argName = argNames.get(i).getText();
                var alreadyDefinedFn = dtNamespace.lookup(argName);
                if (alreadyDefinedFn != null
                        && (!alreadyDefinedFn.sort().equals(argSort)
                                || !alreadyDefinedFn.argSort(0).equals(sort))) {
                    throw new RuntimeException("Name already in namespace: " + argName);
                }
                Function fn = new RFunction(new Name(argName), argSort, new Sort[] { sort }, null,
                    false, false);
                dtNamespace.add(fn);
            }
            Function function = new RFunction(name, sort, args, null, true, false);
            namespaces().functions().addSafely(function);
        }
        namespaces().functions().addSafely(dtNamespace.allElements());
        return null;
    }


    @Override
    public Object visitPred_decl(KeYRustyParser.Pred_declContext ctx) {
        String pred_name = accept(ctx.funcpred_name());
        List<Boolean> whereToBind = accept(ctx.where_to_bind());
        List<Sort> argSorts = accept(ctx.arg_sorts());
        if (whereToBind != null && whereToBind.size() != argSorts.size()) {
            semanticError(ctx, "Where-to-bind list must have same length as argument list");
        }

        Function p = null;

        int separatorIndex = pred_name.indexOf("::");
        if (separatorIndex > 0) {
            String sortName = pred_name.substring(0, separatorIndex);
            String baseName = pred_name.substring(separatorIndex + 2);
            Sort genSort = lookupSort(sortName);
            // if (genSort instanceof GenericSort) {
            // assert argSorts != null;
            // p = SortDependingFunction.createFirstInstance((GenericSort) genSort,
            // new Name(baseName), JavaDLTheory.FORMULA, argSorts.toArray(new Sort[0]), false);
            // }
        }

        if (p == null) {
            assert argSorts != null;
            p = new RFunction(new Name(pred_name), RustyDLTheory.FORMULA,
                argSorts.toArray(new Sort[0]),
                whereToBind == null ? null : whereToBind.toArray(new Boolean[0]), false);
        }

        if (lookup(p.name()) == null) {
            functions().add(p);
        } else {
            // weigl: agreement on KaKeY meeting: this should be an error.
            semanticError(ctx, "Predicate '" + p.name() + "' is already defined!");
        }
        return null;
    }

    @Override
    public Object visitFunc_decl(KeYRustyParser.Func_declContext ctx) {
        boolean unique = ctx.UNIQUE() != null;
        Sort retSort = accept(ctx.sortId());
        String funcName = accept(ctx.funcpred_name());
        List<Boolean[]> whereToBind = accept(ctx.where_to_bind());
        List<Sort> argSorts = accept(ctx.arg_sorts());
        assert argSorts != null;

        if (whereToBind != null && whereToBind.size() != argSorts.size()) {
            semanticError(ctx, "Where-to-bind list must have same length as argument list");
        }

        RFunction f = null;
        assert funcName != null;
        int separatorIndex = funcName.indexOf("::");
        if (separatorIndex > 0) {
            String sortName = funcName.substring(0, separatorIndex);
            String baseName = funcName.substring(separatorIndex + 2);
            Sort genSort = lookupSort(sortName);
            // if (genSort instanceof GenericSort) {
            // f = SortDependingFunction.createFirstInstance((GenericSort) genSort,
            // new Name(baseName), retSort, argSorts.toArray(new Sort[0]), unique);
            // }
        }

        // TODO debug this; why Boolean[]?
        if (f == null) {
            f = new RFunction(new Name(funcName), retSort, argSorts.toArray(new Sort[0]),
                whereToBind == null ? null : whereToBind.toArray(new Boolean[0]), unique);
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
    public Object visitFunc_decls(KeYRustyParser.Func_declsContext ctx) {
        return mapOf(ctx.func_decl());
    }

    public Object visitPred_decls(KeYRustyParser.Pred_declsContext ctx) {
        return mapOf(ctx.pred_decl());
    }

}
