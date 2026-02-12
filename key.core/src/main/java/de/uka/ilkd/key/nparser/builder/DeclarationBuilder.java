/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.builder;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.*;
import de.uka.ilkd.key.nparser.KeYParser;

import org.key_project.logic.Choice;
import org.key_project.logic.HasMeta;
import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.RuleSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Immutables;
import org.key_project.util.java.CollectionUtil;

import org.antlr.v4.runtime.Token;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This visitor evaluates all basic (level 0) declarations. This includes:
 * <ul>
 * <li>Option Declarations</li>
 * <li>Sorts</li>
 * <li>Program variables</li>
 * <li>Schema variables</li>
 * <li>Rulesets</li>
 * </ul>
 * <p>
 * This information is registered into the given {@link NamespaceSet}.
 *
 * @author Alexander Weigl
 * @version 1 (12/4/19)
 * @see FunctionPredicateBuilder for level-1 declarations
 */
public class DeclarationBuilder extends DefaultBuilder {
    private final Map<String, String> category2Default = new HashMap<>();
    private static final Logger LOGGER = LoggerFactory.getLogger(DeclarationBuilder.class);

    public DeclarationBuilder(Services services, NamespaceSet nss) {
        super(services, nss);
    }

    @Override
    public Object visitDecls(KeYParser.DeclsContext ctx) {
        mapMapOf(ctx.option_decls(), ctx.options_choice(), ctx.ruleset_decls(), ctx.sort_decls(),
            ctx.datatype_decls(),
            ctx.prog_var_decls(), ctx.schema_var_decls());
        return null;
    }

    @Override
    public Object visitDatatype_decl(KeYParser.Datatype_declContext ctx) {
        var name = ctx.name.getText();
        var doc = processDocumentation(ctx.doc);
        var origin = BuilderHelpers.getPosition(ctx);
        List<GenericParameter> typeParameters = accept(ctx.formal_sort_param_decls());
        if (typeParameters == null) {
            var s = new SortImpl(new Name(name), ImmutableSet.empty(), false);
            sorts().addSafely(s);
            docsSpace().setDocumentation(s, doc);
            docsSpace().setOrigin(s, origin);
        } else {
            var doubled = CollectionUtil.findDuplicates(typeParameters);
            if (!doubled.isEmpty()) {
                semanticError(ctx.formal_sort_param_decls(),
                    "Type parameters must be unique within a declaration. Found duplicate: %s",
                    doubled.getFirst());
            }
            var s = new ParametricSortDecl(new Name(name), false, ImmutableSet.empty(),
                ImmutableList.fromList(typeParameters));
            namespaces().parametricSorts().addSafely(s);
            docsSpace().setDocumentation(s, doc);
            docsSpace().setOrigin(s, origin);
        }
        return null;
    }

    @Override
    public Object visitProg_var_decls(KeYParser.Prog_var_declsContext ctx) {
        for (int i = 0; i < ctx.simple_ident_comma_list_with_docs().size(); i++) {
            var c = ctx.simple_ident_comma_list_with_docs(i);
            List<String> varNames = c.simple_ident_with_doc()
                    .stream().map(it -> (String) accept(it.simple_ident())).toList();
            KeYJavaType kjt = accept(ctx.keyjavatype(i));
            assert varNames != null;
            for (String varName : varNames) {
                if (varName.equals("null")) {
                    semanticError(c, "Function '" + varName + "' is already defined!");
                }
                ProgramElementName pvName = new ProgramElementName(varName);
                Named name = lookup(pvName);
                if (name != null) {
                    // commented out as pv do not have unique name (at the moment)
                    // throw new AmbigiousDeclException(varName, getSourceName(), getLine(),
                    // getColumn())
                    if (!(name instanceof ProgramVariable pv)
                            || !(pv.getKeYJavaType().equals(kjt))) {
                        programVariables().add(new LocationVariable(pvName, kjt));
                    }
                } else {
                    programVariables().add(new LocationVariable(pvName, kjt));
                }
            }
        }
        return null;
    }


    @Override
    public Object visitChoice(KeYParser.ChoiceContext ctx) {
        String cat = ctx.category.getText();
        String catDoc = processDocumentation(ctx.maindoc);
        docsSpace().setDocumentation(new HasMeta.OptionCategory(cat), catDoc);

        for (KeYParser.OptionDeclContext optdecl : ctx.optionDecl()) {
            Token catctx = optdecl.IDENT;
            String name = cat + ":" + catctx.getText();

            Choice c = choices().lookup(new Name(name));
            if (c == null) {
                c = new Choice(catctx.getText(), cat);
                choices().add(c);

                var doc = processDocumentation(optdecl.DOC_COMMENT);
                docsSpace().setDocumentation(c, doc);
            }
            category2Default.putIfAbsent(cat, name);
        }

        category2Default.computeIfAbsent(cat, it -> {
            choices().add(new Choice(cat + ":On", cat));
            choices().add(new Choice(cat + ":Off", cat));
            return cat + ":On";
        });

        return null;
    }

    @Override
    public Object visitSort_decls(KeYParser.Sort_declsContext ctx) {
        for (KeYParser.One_sort_declContext c : ctx.one_sort_decl()) {
            c.accept(this);
        }
        return null;
    }

    @Override
    public Object visitOne_sort_decl(KeYParser.One_sort_declContext ctx) {
        List<Sort> sortOneOf = accept(ctx.sortOneOf);
        List<Sort> sortExt = accept(ctx.sortExt);
        boolean isGenericSort = ctx.GENERIC() != null;
        boolean isProxySort = ctx.PROXY() != null;
        boolean isAbstractSort = ctx.ABSTRACT() != null;
        List<Sort> createdSorts = new LinkedList<>();
        var sectionDoc = processDocumentation(ctx.DOC_COMMENT());

        ImmutableSet<Sort> ext = sortExt == null ? ImmutableSet.empty()
                : Immutables.createSetFrom(sortExt);

        if (ctx.ALIAS() != null) {
            String aliasId = accept(ctx.simple_ident_dots());
            assert aliasId != null;
            Name name = new Name(aliasId);
            if (namespaces().sorts().lookup(name) != null) {
                semanticError(ctx, "A sort of name %s already exists", name);
            }
            if (namespaces().sortAliases().lookup(name) != null) {
                semanticError(ctx, "A sort alias of name %s already exists", name);
            }
            Sort aliased = accept(ctx.sortId());
            var alias = new SortAlias(name, aliased);
            namespaces().sortAliases().addSafely(alias);
            return alias;
        }

        if (ctx.sortIds != null) {
            for (var idCtx : ctx.sortIds.simple_ident_dots_with_docs()) {
                String sortId = accept(idCtx.simple_ident_dots());
                Name sortName = new Name(sortId);


                ImmutableSet<Sort> oneOf = sortOneOf == null ? ImmutableSet.empty()
                        : Immutables.createSetFrom(sortOneOf);

                // attention: no expand to java.lang here!
                Sort existingSort = sorts().lookup(sortName);
                if (existingSort == null) {
                    Sort s = null;
                    if (isGenericSort) {
                        try {
                            s = new GenericSort(sortName, ext, oneOf);
                        } catch (GenericSupersortException e) {
                            semanticError(ctx, "Illegal sort given");
                        }
                    } else if (new Name("any").equals(sortName)) {
                        s = JavaDLTheory.ANY;
                    } else {
                        if (isProxySort) {
                            s = new ProxySort(sortName, ext);
                        } else {
                            s = new SortImpl(sortName, ext, isAbstractSort);
                        }
                    }
                    assert s != null;
                    String doc = processDocumentation(idCtx.DOC_COMMENT());
                    String origin = BuilderHelpers.getPosition(idCtx);
                    docsSpace().setOrigin(s, origin);
                    docsSpace().setDocumentation(s,
                        Stream.of(doc, sectionDoc).filter(Objects::nonNull)
                                .collect(Collectors.joining("\n")));
                    sorts().add(s);
                    createdSorts.add(s);
                } else {
                    // weigl: agreement on KaKeY meeting: this should be ignored until we finally
                    // have local namespaces for generic sorts
                    // addWarning(ctx, "Sort declaration is ignored, due to collision.");
                    LOGGER.debug(
                        "Sort declaration of {} in {} is ignored due to collision (already "
                            + "present in {}).",
                        sortName, BuilderHelpers.getPosition(ctx),
                        docsSpace().findOrigin(existingSort));
                }
            }
        } else {
            // parametric sort
            var declCtx = ctx.parametric_sort_decl();
            assert declCtx != null : "One of the two must be present";
            List<GenericParameter> typeParams =
                visitFormal_sort_param_decls(declCtx.formal_sort_param_decls());
            ImmutableList<GenericParameter> params = ImmutableList.fromList(typeParams);
            var doubled = CollectionUtil.findDuplicates(params.map(GenericParameter::sort));
            if (!doubled.isEmpty()) {
                semanticError(declCtx,
                    "Type parameters must be unique within a declaration. Found duplicate: %s",
                    doubled.getFirst());
            }
            String name = declCtx.simple_ident_dots().getText();
            Name sortName = new Name(name);
            if (sorts().lookup(sortName) != null) {
                semanticError(declCtx,
                    "Cannot declare parametric sort %s, as a sort of the same name has already been declared",
                    sortName);
            }
            var sortDecl = new ParametricSortDecl(sortName, isAbstractSort, ext, params);
            namespaces().parametricSorts().addSafely(sortDecl);
            docsSpace().setOrigin(sortDecl, BuilderHelpers.getPosition(declCtx));
            var doc = processDocumentation(declCtx.DOC_COMMENT());
            docsSpace().setDocumentation(sortDecl,
                Stream.of(doc, sectionDoc).filter(Objects::nonNull)
                        .collect(Collectors.joining("\n")));
        }
        return createdSorts;
    }

    @Override
    public Object visitOption_decls(KeYParser.Option_declsContext ctx) {
        return mapOf(ctx.choice());
    }

    @Override
    public List<Sort> visitExtends_sorts(KeYParser.Extends_sortsContext ctx) {
        return mapOf(ctx.sortId());
    }

    @Override
    public List<Sort> visitOneof_sorts(KeYParser.Oneof_sortsContext ctx) {
        return mapOf(ctx.sortId());
    }


    @Override
    public Object visitRuleset_decls(KeYParser.Ruleset_declsContext ctx) {
        for (KeYParser.Simple_ident_with_docContext iddoc : ctx.simple_ident_with_doc()) {
            String id = accept(iddoc.simple_ident());
            String doc = processDocumentation(iddoc.DOC_COMMENT());
            RuleSet h = new RuleSet(new Name(id));
            if (ruleSets().lookup(new Name(id)) == null) {
                ruleSets().add(h);
                docsSpace().setDocumentation(h, doc);
            }
        }
        return null;
    }


    @Override
    public Object visitOptions_choice(KeYParser.Options_choiceContext ctx) {
        return null;
    }

}
