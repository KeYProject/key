package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.List;

@NullMarked()
abstract public sealed class BaseAstNode implements AstNode permits Abbreviation, AbstractSortDecl, AccessTerm, ActivatedChoice, Add, AddProgVars, AddRules, AliasDeclimplements, ArgSorts, ArgSortsOrFormula, Attribute, BooleanLiteral, BoundVariables, BraceSuffix, BracketSuffixHeap, BracketTerm, CKV, CKey, CValue, Call, CastTerm, CharLiteral, Choice, ComparisonTerm, ConfigurationFile, ConjunctionTerm, Contracts, DatatypeConstructor, DatatypeDecl, DatatypeDecls, DeclList, Declaration, DisjunctionTerm, ElementaryUpdateTerm, EqualityTerm, EquivalenceTerm, ExtendsSorts, File, FloatLiteral, FormalSortArgs, FormalSortParamDecls, Formula, FuncDecl, FuncDecls, FuncPredName, GenericSortDecl, GoalSpec, GoalSpecs, IfExThenElseTerm, IfThenElseTerm, ImplicationTerm, IncludeStatement, IntegerLiteral, Invariants, KeyJavaType, Label, Literals, LocationTerm, LocsetTerm, ModalityTerm, Modifiers, NegationTerm, OneBoundVariable, OneContract, OneInclude, OneInvariant, OneOfSorts, OneSchemaVarDecl, OneSortDecl, OptionDecls, OptionList, OptionsChoice, ParallelTerm, PredDecl, PredDecls, Preferences, Problem, Profile, ProgVarDecls, Proof, ProofScript, ProofScriptCommand, ProofScriptEntry, ProofScriptParameter, ProxySortDecl, QuantifierTerm, ReplaceWith, RulesOrAxioms, RulesetDecl, RulesetDecls, SchemaModifiers, SchemaVarDecl, SchemaVarDecls, SemiSequent, Seq, SimpleIdentDots, SortDecls, SortId, StringLiteral, StrongArithTerm1, StrongArithTerm2, StubAstNodes, SubstitutionTerm, Taclet, Term, TermOrSeq, TransformDecl, TransformDecls, Triggers, UnaryMinusTerm, UpdateTerm, Varexp, VarexpList, WeakArithTerm, WhereToBind {
    @Nullable()
    abstract Position position();

    abstract BaseAstNode setPosition(@Nullable() Position value);

    public BaseAstNode() {
    }
}
