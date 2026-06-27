/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import de.uka.ilkd.key.peg.ast.StubAstNodes.*;

/**
 * Visitor interface for traversing the KeY PEG AST.
 *
 * @param <T> The return type of the visitor
 * @author Cline
 * @version 1.0
 */
@NullMarked
public interface AstVisitor<T> {
    // File structure
    T visit(File file);
    T visit(DeclList decls);
    T visit(Problem problem);
    T visit(Proof proof);
    T visit(Profile profile);
    T visit(Preferences preferences);

    // Include statements
    T visit(IncludeStatement include);
    T visit(OneInclude oneInclude);

    // Options
    T visit(OptionsChoice optionsChoice);
    T visit(ActivatedChoice activatedChoice);
    T visit(OptionDecls optionDecls);
    T visit(Choice choice);

    // Sort declarations
    T visit(SortDecls sortDecls);
    T visit(OneSortDecl oneSortDecl);
    T visit(SimpleIdentDots simpleIdentDots);
    T visit(ExtendsSorts extendsSorts);
    T visit(OneOfSorts oneOfSorts);
    T visit(KeyJavaType keyJavaType);
    T visit(GenericSortDecl genericSortDecl);
    T visit(ProxySortDecl proxySortDecl);
    T visit(AbstractSortDecl abstractSortDecl);
    T visit(AliasDecl aliasDecl);

    // Variable declarations
    T visit(ProgVarDecls progVarDecls);
    T visit(SchemaVarDecls schemaVarDecls);
    T visit(OneSchemaVarDecl oneSchemaVarDecl);
    T visit(SchemaVarDecl schemaVarDecl);
    T visit(SchemaModifiers schemaModifiers);

    // Function and Predicate declarations
    T visit(PredDecls predDecls);
    T visit(PredDecl predDecl);
    T visit(FuncDecls funcDecls);
    T visit(FuncDecl funcDecl);
    T visit(FuncPredName funcPredName);
    T visit(ArgSorts argSorts);
    T visit(WhereToBind whereToBind);
    T visit(ArgSortsOrFormula argSortsOrFormula);
    T visit(FormalSortParamDecls formalSortParamDecls);
    T visit(TransformDecls transformDecls);
    T visit(TransformDecl transformDecl);

    // Datatype declarations
    T visit(DatatypeDecls datatypeDecls);
    T visit(DatatypeDecl datatypeDecl);
    T visit(DatatypeConstructor constructor);

    // Ruleset declarations
    T visit(RulesetDecls rulesetDecls);
    T visit(RulesetDecl rulesetDecl);

    // Taclet-related
    T visit(Taclet taclet);
    T visit(Modifiers modifiers);
    T visit(Seq seq);
    T visit(TermOrSeq termOrSeq);
    T visit(SemiSequent semiSequent);
    T visit(GoalSpecs goalSpecs);
    T visit(GoalSpec goalSpec);
    T visit(ReplaceWith replaceWith);
    T visit(Add add);
    T visit(AddRules addRules);
    T visit(AddProgVars addProgVars);
    T visit(Triggers triggers);
    T visit(VarexpList varexpList);
    T visit(Varexp varexp);
    T visit(OptionList optionList);

    // Terms and formulas
    T visit(Term term);
    T visit(Literals literals);
    T visit(BooleanLiteral booleanLiteral);
    T visit(IntegerLiteral integerLiteral);
    T visit(FloatLiteral floatLiteral);
    T visit(StringLiteral stringLiteral);
    T visit(CharLiteral charLiteral);
    T visit(ParallelTerm parallelTerm);
    T visit(ElementaryUpdateTerm elementaryUpdateTerm);
    T visit(EquivalenceTerm equivalenceTerm);
    T visit(ImplicationTerm implicationTerm);
    T visit(DisjunctionTerm disjunctionTerm);
    T visit(ConjunctionTerm conjunctionTerm);
    T visit(NegationTerm negationTerm);
    T visit(QuantifierTerm quantifierTerm);
    T visit(ModalityTerm modalityTerm);
    T visit(EqualityTerm equalityTerm);
    T visit(ComparisonTerm comparisonTerm);
    T visit(WeakArithTerm weakArithTerm);
    T visit(StrongArithTerm1 strongArithTerm1);
    T visit(StrongArithTerm2 strongArithTerm2);
    T visit(UpdateTerm updateTerm);
    T visit(SubstitutionTerm substitutionTerm);
    T visit(CastTerm castTerm);
    T visit(UnaryMinusTerm unaryMinusTerm);
    T visit(BracketTerm bracketTerm);
    T visit(BracketSuffixHeap bracketSuffixHeap);
    T visit(BraceSuffix braceSuffix);
    T visit(Attribute attribute);
    T visit(Call call);
    T visit(Label label);
    T visit(LocationTerm locationTerm);
    T visit(LocsetTerm locsetTerm);
    T visit(BoundVariables boundVariables);
    T visit(OneBoundVariable oneBoundVariable);

    // Contracts and Invariants
    T visit(Contracts contracts);
    T visit(OneContract oneContract);
    T visit(Invariants invariants);
    T visit(OneInvariant oneInvariant);

    // Rules and Axioms
    T visit(RulesOrAxioms rulesOrAxioms);
    T visit(Formula formula);

    // Configuration
    T visit(ConfigurationFile cfile);
    T visit(CKV ckv);
    T visit(CValue cvalue);
    T visit(CKey ckey);

    // Proof Script
    T visit(ProofScriptEntry proofScriptEntry);
    T visit(ProofScript proofScript);
    T visit(ProofScriptCommand proofScriptCommand);
    T visit(ProofScriptParameter proofScriptParameter);

    T visit(SortId sortId);

    T visit(GoalSpecWithOption goalSpecWithOption);

    T visit(StubAstNodes.GoalSpec goalSpec);

    T visit(StubAstNodes.ReplaceWith replaceWith);

    T visit(StubAstNodes.Add add);

    T visit(StubAstNodes.AddRules addRules);
    T visit(AstNode top);
}
