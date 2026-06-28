package org.key_project.key.ast.visitor;

import org.key_project.key.ast.*;
import java.util.*;

public interface ArgVisitor<R, A> {

    R visit(Abbreviation n, A arg);

    R visit(AbstractSortDecl n, A arg);

    R visit(AccessTerm n, A arg);

    R visit(ActivatedChoice n, A arg);

    R visit(Add n, A arg);

    R visit(AddProgVars n, A arg);

    R visit(AddRules n, A arg);

    R visit(AliasDeclimplements n, A arg);

    R visit(ArgSorts n, A arg);

    R visit(ArgSortsOrFormula n, A arg);

    R visit(Attribute n, A arg);

    R visit(BooleanLiteral n, A arg);

    R visit(BoundVariables n, A arg);

    R visit(BraceSuffix n, A arg);

    R visit(BracketSuffixHeap n, A arg);

    R visit(BracketTerm n, A arg);

    R visit(Call n, A arg);

    R visit(CastTerm n, A arg);

    R visit(CharLiteral n, A arg);

    R visit(Choice n, A arg);

    R visit(CKey n, A arg);

    R visit(CKV n, A arg);

    R visit(ComparisonTerm n, A arg);

    R visit(ConfigurationFile n, A arg);

    R visit(ConjunctionTerm n, A arg);

    R visit(Contracts n, A arg);

    R visit(CValue n, A arg);

    R visit(DatatypeConstructor n, A arg);

    R visit(DatatypeDecl n, A arg);

    R visit(DatatypeDecls n, A arg);

    R visit(DeclList n, A arg);

    R visit(DisjunctionTerm n, A arg);

    R visit(ElementaryUpdateTerm n, A arg);

    R visit(EqualityTerm n, A arg);

    R visit(EquivalenceTerm n, A arg);

    R visit(ExtendsSorts n, A arg);

    R visit(File n, A arg);

    R visit(FloatLiteral n, A arg);

    R visit(FormalSortArgs n, A arg);

    R visit(FormalSortParamDecls n, A arg);

    R visit(Formula n, A arg);

    R visit(FuncDecl n, A arg);

    R visit(FuncDecls n, A arg);

    R visit(FuncPredName n, A arg);

    R visit(GenericSortDecl n, A arg);

    R visit(GoalSpec n, A arg);

    R visit(GoalSpecs n, A arg);

    R visit(IfExThenElseTerm n, A arg);

    R visit(IfThenElseTerm n, A arg);

    R visit(ImplicationTerm n, A arg);

    R visit(IncludeStatement n, A arg);

    R visit(IntegerLiteral n, A arg);

    R visit(Invariants n, A arg);

    R visit(KeyJavaType n, A arg);

    R visit(Label n, A arg);

    R visit(LocationTerm n, A arg);

    R visit(LocsetTerm n, A arg);

    R visit(ModalityTerm n, A arg);

    R visit(Modifiers n, A arg);

    R visit(NegationTerm n, A arg);

    R visit(OneBoundVariable n, A arg);

    R visit(OneContract n, A arg);

    R visit(OneInclude n, A arg);

    R visit(OneInvariant n, A arg);

    R visit(OneOfSorts n, A arg);

    R visit(OneSchemaVarDecl n, A arg);

    R visit(OptionDecls n, A arg);

    R visit(OptionList n, A arg);

    R visit(OptionsChoice n, A arg);

    R visit(ParallelTerm n, A arg);

    R visit(PredDecl n, A arg);

    R visit(PredDecls n, A arg);

    R visit(Preferences n, A arg);

    R visit(Problem n, A arg);

    R visit(Profile n, A arg);

    R visit(ProgVarDecls n, A arg);

    R visit(Proof n, A arg);

    R visit(ProofScriptCommand n, A arg);

    R visit(ProofScriptEntry n, A arg);

    R visit(ProofScript n, A arg);

    R visit(ProofScriptParameter n, A arg);

    R visit(ProxySortDecl n, A arg);

    R visit(QuantifierTerm n, A arg);

    R visit(ReplaceWith n, A arg);

    R visit(RulesetDecl n, A arg);

    R visit(RulesetDecls n, A arg);

    R visit(RulesOrAxioms n, A arg);

    R visit(SchemaModifiers n, A arg);

    R visit(SchemaVarDecl n, A arg);

    R visit(SchemaVarDecls n, A arg);

    R visit(SemiSequent n, A arg);

    R visit(Seq n, A arg);

    R visit(SimpleIdentDots n, A arg);

    R visit(SortDecls n, A arg);

    R visit(SortId n, A arg);

    R visit(StringLiteral n, A arg);

    R visit(StrongArithTerm1 n, A arg);

    R visit(StrongArithTerm2 n, A arg);

    R visit(StubAstNodes n, A arg);

    R visit(SubstitutionTerm n, A arg);

    R visit(Taclet n, A arg);

    R visit(Term n, A arg);

    R visit(TermOrSeq n, A arg);

    R visit(TransformDecl n, A arg);

    R visit(TransformDecls n, A arg);

    R visit(Triggers n, A arg);

    R visit(UnaryMinusTerm n, A arg);

    R visit(UpdateTerm n, A arg);

    R visit(Varexp n, A arg);

    R visit(VarexpList n, A arg);

    R visit(WeakArithTerm n, A arg);

    R visit(WhereToBind n, A arg);
}
