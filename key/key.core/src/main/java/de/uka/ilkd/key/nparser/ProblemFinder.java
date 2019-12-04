package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.*;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import java.util.ArrayList;
import java.util.List;

@SuppressWarnings("unchecked")
public class ProblemFinder extends ExpressionBuilder {
    private Term problemTerm;
    private String choosedContract;
    private String proofObligation;

    public ProblemFinder(Services services, NamespaceSet nss) {
        super(services, nss);
    }

    /*
    private Set<LocationVariable> progVars(JavaBlock jb) {
        ProgramVariableCollector pvc = new ProgramVariableCollector(jb.program(), getServices());
        pvc.start();
        return pvc.result();
    }
     */


    private List<Sort> createSort(boolean isAbstractSort, boolean isGenericSort, boolean isProxySort,
                                  Sort[] sortExt, Sort[] sortOneOf, List<String> sortIds) {
        List<Sort> createdSorts = new ArrayList<>(5);
        for (String sortId : sortIds) {
            Name sort_name = new Name(sortId);
            // attention: no expand to java.lang here!
            if (sorts().lookup(sort_name) == null) {
                Sort s = null;
                if (isGenericSort) {
                    int i;
                    ImmutableSet<Sort> ext = DefaultImmutableSet.nil();
                    ImmutableSet<Sort> oneOf = DefaultImmutableSet.nil();

                    for (i = 0; i != sortExt.length; ++i)
                        ext = ext.add(sortExt[i]);

                    for (i = 0; i != sortOneOf.length; ++i)
                        oneOf = oneOf.add(sortOneOf[i]);

                    try {
                        s = new GenericSort(sort_name, ext, oneOf);
                    } catch (GenericSupersortException e) {
                        throw new BuildingException("Illegal sort given", e);
                    }
                } else if (new Name("any").equals(sort_name)) {
                    s = Sort.ANY;
                } else {
                    ImmutableSet<Sort> ext = DefaultImmutableSet.nil();

                    for (int i = 0; i != sortExt.length; ++i) {
                        ext = ext.add(sortExt[i]);
                    }

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
    public Object visitFile(KeYParser.FileContext ctx) {
        each(ctx.problem());
        return null;
    }

    @Override
    public KeYJavaType visitArrayopid(KeYParser.ArrayopidContext ctx) {
        return (KeYJavaType) accept(ctx.keyjavatype());
    }

    /*
    @Override
    public IdDeclaration visitId_declaration(KeYParser.Id_declarationContext ctx) {
        var id = (String) ctx.IDENT().getText();
        var s = (Sort) (ctx.sortId_check() != null ? accept(ctx.sortId_check()) : null);
        return new IdDeclaration(id, s);
    }
    */

    @Override
    public Term visitProblem(KeYParser.ProblemContext ctx) {
        if (ctx.CHOOSECONTRACT() != null) {
            if (ctx.chooseContract != null)
                choosedContract = accept(ctx.chooseContract);
        }
        if (ctx.PROOFOBLIGATION() != null) {
            if (ctx.proofObligation != null)
                proofObligation = accept(ctx.proofObligation);
        }
        if (ctx.PROBLEM() != null) {
            problemTerm = accept(ctx.formula());
        }
        return null;
    }

    public String getChoosedContract() {
        return choosedContract;
    }

    public String getProofObligation() {
        return proofObligation;
    }

    public Term getProblemTerm() {
        return problemTerm;
    }
}
