package de.uka.ilkd.key.nparser;

import antlr.RecognitionException;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.JavaReader;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.*;
import de.uka.ilkd.key.parser.AmbigiousDeclException;
import de.uka.ilkd.key.parser.NotDeclException;
import de.uka.ilkd.key.parser.SchemaVariableModifierSet;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.dl.translation.DLSpecFactory;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

@SuppressWarnings("unchecked")
public class ProblemFinder extends ExpressionBuilder {
    private Term problemTerm;
    private IProgramMethod pm = null;
    private List<Contract> contracts = new ArrayList<>();
    private ImmutableSet<ClassInvariant> invs = DefaultImmutableSet.nil();
    private ParsableVariable selfVar;
    private JavaReader javaReader;
    private List<Object> invariants;
    private List<Object> seqChoices;

    public ProblemFinder(Services services, NamespaceSet nss) {
        super(services, nss);
    }

    public List<Contract> getContracts() {
        return contracts;
    }

    public ImmutableSet<ClassInvariant> getInvariants() {
        return invs;
    }


    private Set<LocationVariable> progVars(JavaBlock jb) {
        ProgramVariableCollector pvc = new ProgramVariableCollector(jb.program(), getServices());
        pvc.start();
        return pvc.result();
    }


    /**
     * returns the ProgramMethod parsed in the jml_specifications section.
     */
    public IProgramMethod getProgramMethod() {
        return pm;
    }




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
    public Object visitDecls(KeYParser.DeclsContext ctx) {
        activatedChoices = DefaultImmutableSet.nil();
        allOf(ctx.one_include_statement(), ctx.one_include_statement());
/*
        allOf(ctx.options_choice(), ctx.option_decls(), ctx.sort_decls(),
                ctx.prog_var_decls(), ctx.schema_var_decls(), ctx.ruleset_decls());
        allOf(ctx.pred_decls(), ctx.func_decls(), ctx.transform_decls());
        allOf(ctx.rulesOrAxioms());
                */
        contracts = allOf(ctx.contracts());
        invariants = allOf(ctx.invariants());
        seqChoices = allOf(ctx.options_choice());
        return null;
    }

    /*@Override
    public Choice visitActivated_choice(KeYParser.Activated_choiceContext ctx) {
        var cat = ctx.cat.getText();
        var ch = ctx.choice_.getText();
        if (usedChoiceCategories.contains(cat)) {
            throw new IllegalArgumentException("You have already chosen a different option for " + cat);
        }
        usedChoiceCategories.add(cat);
        var name = cat + ":" + ch;
        var c = (Choice) choices().lookup(new Name(name));
        if (c == null) {
            throwEx(new NotDeclException(null, "Option", ch));
        } else {
            activatedChoices = activatedChoices.add(c);
        }
        return c;
    }*/



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
    public Object visitContracts(KeYParser.ContractsContext ctx) {
        return allOf(ctx.one_contract());
    }

    @Override
    public Object visitInvariants(KeYParser.InvariantsContext ctx) {
        Namespace<QuantifiableVariable> orig = variables();
        selfVar = (ParsableVariable) ctx.selfVar.accept(this);
        ctx.one_invariant().forEach(it -> it.accept(this));
        unbindVars(orig);
        return null;
    }

    @Override
    public Object visitOne_contract(KeYParser.One_contractContext ctx) {
        String contractName = visitSimple_ident(ctx.contractName);
        //for program variable declarations
        namespaces().setProgramVariables(new Namespace(programVariables()));
        var fma = visitFormula(ctx.formula());
        var modifiesClause = visitTerm(ctx.modifiesClause);
        DLSpecFactory dsf = new DLSpecFactory(getServices());
        try {
            contracts.add(dsf.createDLOperationContract(contractName, fma, modifiesClause));
        } catch (ProofInputException e) {
            semanticError(ctx, e.getMessage());
        }
        //dump local program variable declarations
        namespaces().setProgramVariables(programVariables().parent());
        return null;
    }

    @Override
    public Object visitOne_invariant(KeYParser.One_invariantContext ctx) {
        String invName = visitSimple_ident(ctx.simple_ident());
        Term fma = accept(ctx.formula());
        var displayName = ctx.displayName != null ? ctx.displayName.getText() : null;
        DLSpecFactory dsf = new DLSpecFactory(getServices());
        try {
            invs = invs.add(dsf.createDLClassInvariant(invName,
                    displayName,
                    selfVar,
                    fma));
        } catch (ProofInputException e) {
            semanticError(ctx, e.getMessage());
        }
        return null;
    }

    @Override
    public Term visitProblem(KeYParser.ProblemContext ctx) {
        /*DefaultImmutableSet<Choice> choices = DefaultImmutableSet.nil();
        if (ctx.CHOOSECONTRACT() != null) {
            if (ctx.chooseContract != null)
                parsedKeyFile.setChooseContract(accept(ctx.chooseContract));
            else
                parsedKeyFile.setChooseContract("");
        }
        if (ctx.PROOFOBLIGATION() != null) {
            if (ctx.proofObligation != null)
                parsedKeyFile.setProofObligation(accept(ctx.proofObligation));
            else
                parsedKeyFile.setProofObligation("");
        }*/
        if (ctx.PROBLEM() != null) {
            problemTerm = accept(ctx.formula());
        }
        return null;
    }
}
