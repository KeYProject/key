/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.builder;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.nparser.KeYParser;

import org.key_project.util.collection.ImmutableArray;


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
public class FunctionPredicateBuilder extends DefaultBuilder {
    public FunctionPredicateBuilder(Services services, NamespaceSet nss) {
        super(services, nss);
    }

    @Override
    public Object visitFile(KeYParser.FileContext ctx) {
        return accept(ctx.decls());
    }

    @Override
    public Object visitDecls(KeYParser.DeclsContext ctx) {
        mapMapOf(ctx.pred_decls(), ctx.func_decls(), ctx.transform_decls());
        return null;
    }

    @Override
    public Object visitPred_decl(KeYParser.Pred_declContext ctx) {
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
            if (genSort instanceof GenericSort) {
                assert argSorts != null;
                p = SortDependingFunction.createFirstInstance((GenericSort) genSort,
                    new Name(baseName), Sort.FORMULA, argSorts.toArray(new Sort[0]), false);
            }
        }

        if (p == null) {
            assert argSorts != null;
            p = new Function(new Name(pred_name), Sort.FORMULA, argSorts.toArray(new Sort[0]),
                whereToBind == null ? null : whereToBind.toArray(new Boolean[0]), false);
        }

        if (lookup(p.name()) == null) {
            functions().add(p);
        }
        return null;
    }

    @Override
    public Object visitFunc_decl(KeYParser.Func_declContext ctx) {
        boolean unique = ctx.UNIQUE() != null;
        Sort retSort = accept(ctx.sortId());
        String func_name = accept(ctx.funcpred_name());
        List<Boolean[]> whereToBind = accept(ctx.where_to_bind());
        List<Sort> argSorts = accept(ctx.arg_sorts());
        assert argSorts != null;

        if (whereToBind != null && whereToBind.size() != argSorts.size()) {
            semanticError(ctx, "Where-to-bind list must have same length as argument list");
        }

        Function f = null;
        assert func_name != null;
        int separatorIndex = func_name.indexOf("::");
        if (separatorIndex > 0) {
            String sortName = func_name.substring(0, separatorIndex);
            String baseName = func_name.substring(separatorIndex + 2);
            Sort genSort = lookupSort(sortName);
            if (genSort instanceof GenericSort) {
                f = SortDependingFunction.createFirstInstance((GenericSort) genSort,
                    new Name(baseName), retSort, argSorts.toArray(new Sort[0]), unique);
            }
        }

        if (f == null) {
            f = new Function(new Name(func_name), retSort, argSorts.toArray(new Sort[0]),
                whereToBind == null ? null : whereToBind.toArray(new Boolean[0]), unique);
        }

        if (lookup(f.name()) == null) {
            functions().add(f);
        } else {
            addWarning("Function '" + func_name + "' is already defined!");
        }
        return f;
    }

    @Override
    public Object visitFunc_decls(KeYParser.Func_declsContext ctx) {
        return mapOf(ctx.func_decl());
    }


    @Override
    public Object visitTransform_decl(KeYParser.Transform_declContext ctx) {
        Sort retSort = ctx.FORMULA() != null ? Sort.FORMULA : accept(ctx.sortId());
        String trans_name = accept(ctx.funcpred_name());
        List<Sort> argSorts = accept(ctx.arg_sorts_or_formula());
        Transformer t =
            new Transformer(new Name(trans_name), retSort, new ImmutableArray<>(argSorts));
        if (lookup(t.name()) == null) {
            functions().add(t);
        }
        return null;
    }


    @Override
    public Object visitTransform_decls(KeYParser.Transform_declsContext ctx) {
        return mapOf(ctx.transform_decl());
    }


    @Override
    public Object visitPred_decls(KeYParser.Pred_declsContext ctx) {
        return mapOf(ctx.pred_decl());
    }
}
