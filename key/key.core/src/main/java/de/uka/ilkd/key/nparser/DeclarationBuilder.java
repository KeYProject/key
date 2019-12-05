package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.*;
import de.uka.ilkd.key.rule.RuleSet;
import org.antlr.v4.runtime.Token;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import java.util.LinkedList;
import java.util.List;

public class DeclarationBuilder extends DefaultBuilder {
    public DeclarationBuilder(Services services, NamespaceSet nss) {
        super(services, nss);
    }

    @Override
    public Object visitDecls(KeYParser.DeclsContext ctx) {
        mapMapOf(ctx.options_choice(), ctx.option_decls(), ctx.sort_decls(),
                ctx.prog_var_decls(), ctx.schema_var_decls(), ctx.ruleset_decls());
        return null;
    }

    @Override
    public Object visitProg_var_decls(KeYParser.Prog_var_declsContext ctx) {
        String var_name;

        for (int i = 0; i < ctx.simple_ident_comma_list().size(); i++) {
            var var_names = (List<String>) accept(ctx.simple_ident_comma_list(i));
            var kjt = (KeYJavaType) accept(ctx.keyjavatype(i));
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
                        namespaces().programVariables().add(new LocationVariable
                                (pvName, kjt));
                    }
                } else {
                    namespaces().programVariables().add(new LocationVariable
                            (pvName, kjt));
                }
            }
        }
        return null;
    }


    @Override
    public Object visitChoice(KeYParser.ChoiceContext ctx) {
        String cat = ctx.category.getText();
        //System.out.println("choice: " + cat);
        for (Token catctx : ctx.choice_option) {
            var name = cat + ":" + catctx.getText();
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
        ImmutableList<Sort> lsorts = ImmutableSLList.nil();
        //TODO multipleSorts = ImmutableSLList.<Sort>nil();
        for (KeYParser.One_sort_declContext c : ctx.one_sort_decl()) {
            c.accept(this);
        }
        return null;
    }

    @Override
    public Object visitOne_sort_decl(KeYParser.One_sort_declContext ctx) {
        List<String> sortIds = accept(ctx.sortIds);
        List<Sort> sortOneOf = accept(ctx.sortOneOf);
        List<Sort> sortExt = accept(ctx.sortExt);
        boolean isGenericSort = ctx.GENERIC() != null;
        boolean isProxySort = ctx.PROXY() != null;
        boolean isAbstractSort = ctx.ABSTRACT() != null;
        List<Sort> createdSorts = new LinkedList<>();
        for (String sortId : sortIds) {
            Name sort_name = new Name(sortId);

            ImmutableSet<Sort> ext =
                    sortExt == null ? ImmutableSet.empty() :
                            DefaultImmutableSet.fromCollection(sortExt);
            ImmutableSet<Sort> oneOf =
                    sortOneOf == null ? ImmutableSet.empty() :
                            DefaultImmutableSet.fromCollection(sortOneOf);

            // attention: no expand to java.lang here!
            if (sorts().lookup(sort_name) == null) {
                Sort s = null;
                if (isGenericSort) {
                    int i;

                    try {
                        s = new GenericSort(sort_name, ext, oneOf);
                    } catch (GenericSupersortException e) {
                        semanticError(ctx, "Illegal sort given");
                    }
                } else if (new Name("any").equals(sort_name)) {
                    s = Sort.ANY;
                } else {
                    if (isProxySort) {
                        s = new ProxySort(sort_name, ext);
                    } else {
                        s = new SortImpl(sort_name, ext, isAbstractSort);
                    }
                }
                assert s != null;
                sorts().add(s);
                createdSorts.add(s);
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
        return mapOf(ctx.any_sortId_check());
    }

    @Override
    public List<Sort> visitOneof_sorts(KeYParser.Oneof_sortsContext ctx) {
        return mapOf(ctx.sortId_check());
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
