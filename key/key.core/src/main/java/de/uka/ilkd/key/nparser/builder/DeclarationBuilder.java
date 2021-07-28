package de.uka.ilkd.key.nparser.builder;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.*;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.util.Pair;
import org.antlr.v4.runtime.Token;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.java.StringUtil;

import java.util.*;
import java.util.stream.Collector;
import java.util.stream.Collectors;

/**
 * This visitor evaluates all basic (level 0) declarations.
 * This includes:
 * <ul>
 *     <li>Option Declarations</li>
 *     <li>Sorts</li>
 *     <li>Program variables</li>
 *     <li>Schema variables</li>
 *     <li>Rulesets</li>
 * </ul>
 * <p>
 * These information are registered into the given {@link NamespaceSet}.
 *
 * @author Alexander Weigl
 * @version 1 (12/4/19)
 * @see FunctionPredicateBuilder for level-1 declarations
 */
public class DeclarationBuilder extends DefaultBuilder {
    private Map<String, String> category2Default = new HashMap<>();

    public DeclarationBuilder(Services services, NamespaceSet nss) {
        super(services, nss);
    }

    @Override
    public Object visitDecls(KeYParser.DeclsContext ctx) {
        mapMapOf(ctx.option_decls(), ctx.options_choice(),
                ctx.ruleset_decls(), ctx.sort_decls(),
                ctx.prog_var_decls(), ctx.schema_var_decls());
        return null;
    }

    @Override
    public Object visitProg_var_decls(KeYParser.Prog_var_declsContext ctx) {
        String var_name;
        for (int i = 0; i < ctx.simple_ident_comma_list().size(); i++) {
            List<String> var_names = (List<String>) accept(ctx.simple_ident_comma_list(i));
            KeYJavaType kjt = (KeYJavaType) accept(ctx.keyjavatype(i));
            assert var_names != null;
            for (String varName : var_names) {
                var_name = varName;
                ProgramElementName pvName = new ProgramElementName(var_name);
                Named name = lookup(pvName);
                if (name != null) {
                    // commented out as pv do not have unique name (at the moment)
                    //  throw new AmbigiousDeclException
                    //  	(var_name, getSourceName(), getLine(), getColumn());
                    if (!(name instanceof ProgramVariable) || (name instanceof ProgramVariable &&
                            !((ProgramVariable) name).getKeYJavaType().equals(kjt))) {
                        programVariables().add(new LocationVariable
                                (pvName, kjt));
                    }
                } else {
                    programVariables()
                            .add(new LocationVariable(pvName, kjt));
                }
            }
        }
        return null;
    }


    @Override
    public Object visitChoice(KeYParser.ChoiceContext ctx) {
        String cat = ctx.category.getText();
        //System.out.println("choice: " + cat);
        for (KeYParser.OptionDeclContext optdecl : ctx.optionDecl()) {
            Token catctx = optdecl.IDENT;
            String name = cat + ":" + catctx.getText();
            Choice c = choices().lookup(new Name(name));
            if (c == null) {
                c = new Choice(catctx.getText(), cat);
                choices().add(c);
            }
            if (!category2Default.containsKey(cat)) {
                category2Default.put(cat, name);
            }
        }
        if (!category2Default.containsKey(cat)) {
            choices().add(new Choice("On", cat));
            choices().add(new Choice("Off", cat));
            category2Default.put(cat, cat + ":On");
        }
        return null;
    }

    /*@Override
    public Object visitChoice_option(KeYParser.Choice_optionContext ctx) {
        String name = currentChoiceCategory + ":" + ctx.choice_.getText();
        Choice c = choices().lookup(new Name(name));
        if (c == null) {
            c = new Choice(ctx.choice_.getText(), currentChoiceCategory);
            choices().add(c);
        }
        if (!category2Default.containsKey(currentChoiceCategory)) {
            category2Default.put(currentChoiceCategory, name);
        }
        return c;
    }*/

    @Override
    public Object visitSort_decls(KeYParser.Sort_declsContext ctx) {
        for (KeYParser.One_sort_declContext c : ctx.one_sort_decl()) {
            c.accept(this);
        }
        return null;
    }

    @Override
    public List<Pair<String, List<Pair<ParametricSort.Variance, Sort>>>> visitSortList(KeYParser.SortListContext ctx) {
        List<Pair<String, List<Pair<ParametricSort.Variance, Sort>>>> seq = new ArrayList<>();
        for (KeYParser.SortIdContext context : ctx.sortId()) {
            String sortName = context.simple_ident_dots().getText();
            String brackets = StringUtil.repeat("[]", context.EMPTYBRACKETS().size());
            List<Pair<ParametricSort.Variance, Sort>> typeParams = accept(context.formal_sort_parameters());
            seq.add(new Pair<>(sortName, typeParams != null ? typeParams : Collections.emptyList()));
        }
        return seq;
    }


    @Override
    public Object visitOne_sort_decl(KeYParser.One_sort_declContext ctx) {
        List<Pair<String, List<Pair<ParametricSort.Variance, Sort>>>> sortIds = accept(ctx.sortIds);
        List<Sort> sortOneOf = accept(ctx.sortOneOf);
        List<Sort> sortExt = accept(ctx.sortExt);
        boolean isGenericSort = ctx.GENERIC() != null;
        boolean isProxySort = ctx.PROXY() != null;
        boolean isAbstractSort = ctx.ABSTRACT() != null;
        List<Sort> createdSorts = new LinkedList<>();
        assert sortIds != null;

        for (Pair<String, List<Pair<ParametricSort.Variance, Sort>>> sortId : sortIds) {
            Name sortName = new Name(sortId.first);
            boolean isParametricSort = !sortId.second.isEmpty();

            ImmutableSet<Sort> ext =
                    sortExt == null ? ImmutableSet.empty() :
                            DefaultImmutableSet.fromCollection(sortExt);
            ImmutableSet<Sort> oneOf =
                    sortOneOf == null ? ImmutableSet.empty() :
                            DefaultImmutableSet.fromCollection(sortOneOf);

            // attention: no expand to java.lang here!
            if (sorts().lookup(sortName) == null) {
                Sort s = null;
                if(isParametricSort) {
                    if(isGenericSort) {
                        semanticError(ctx, "Generic sorts are not allowed to have type parameters.");
                    }

                    for (Pair<ParametricSort.Variance, Sort> param : sortId.second) {
                        if (!(param.second instanceof GenericSort)) {
                            semanticError(ctx, "Type parameters must be generic sorts. Given type '%s' is %s",
                                    param.second.name(), param.second.getClass().getName());
                        }
                    }

                    ImmutableList<Pair<GenericSort, ParametricSort.Variance>> typeParams =
                            sortId.second.stream().map(it ->
                                    new Pair<>((GenericSort) it.second, it.first))
                                    .collect(ImmutableSLList.toImmutableList());
                    s = new ParametricSort(sortName, ext, isAbstractSort, typeParams);
                }else if (isGenericSort) {
                    int i;

                    try {
                        s = new GenericSort(sortName, ext, oneOf);
                    } catch (GenericSupersortException e) {
                        semanticError(ctx, "Illegal sort given");
                    }
                } else if (new Name("any").equals(sortName)) {
                    s = Sort.ANY;
                } else {
                    if (isProxySort) {
                        s = new ProxySort(sortName, ext);
                    } else {
                        s = new SortImpl(sortName, ext, isAbstractSort);
                    }
                }
                assert s != null;
                sorts().add(s);
                createdSorts.add(s);
            } else {
                addWarning(ctx, "Sort declaration is ignored, due to collision.");
            }
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
        for (String id : this.<String>mapOf(ctx.simple_ident())) {
            RuleSet h = new RuleSet(new Name(id));
            if (ruleSets().lookup(new Name(id)) == null) {
                ruleSets().add(h);
            }
        }
        return null;
    }


    @Override
    public Object visitOptions_choice(KeYParser.Options_choiceContext ctx) {
        //mapOf(ctx.activated_choice());
        return null;
    }


}
