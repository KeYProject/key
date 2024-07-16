/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.builder;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.NamespaceSet;
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
}
