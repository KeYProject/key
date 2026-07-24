package org.key_project.key.ast.visitor;

import org.key_project.key.ast.*;
import java.util.*;

public interface Visitor<R> {

    R visit(Abbreviation n);

    R visit(AbstractSortDecl n);

    R visit(AccessTerm n);

    R visit(ActivatedChoice n);

    R visit(Add n);

    R visit(AddProgVars n);

    R visit(AddRules n);

    R visit(AliasDeclimplements n);

    R visit(ArgSorts n);

    R visit(ArgSortsOrFormula n);

    R visit(Attribute n);

    R visit(BooleanLiteral n);

    R visit(BoundVariables n);

    R visit(BraceSuffix n);

    R visit(BracketSuffixHeap n);

    R visit(BracketTerm n);

    R visit(Call n);

    R visit(CastTerm n);

    R visit(CharLiteral n);

    R visit(Choice n);

    R visit(CKey n);

    R visit(CKV n);

    R visit(ComparisonTerm n);

    R visit(ConfigurationFile n);

    R visit(ConjunctionTerm n);

    R visit(Contracts n);

    R visit(CValue n);

    R visit(DatatypeConstructor n);

    R visit(DatatypeDecl n);

    R visit(DatatypeDecls n);

    R visit(DeclList n);

    R visit(DisjunctionTerm n);

    R visit(ElementaryUpdateTerm n);

    R visit(EqualityTerm n);

    R visit(EquivalenceTerm n);

    R visit(ExtendsSorts n);

    R visit(File n);

    R visit(FloatLiteral n);

    R visit(FormalSortArgs n);

    R visit(FormalSortParamDecls n);

    R visit(Formula n);

    R visit(FuncDecl n);

    R visit(FuncDecls n);

    R visit(FuncPredName n);

    R visit(GenericSortDecl n);

    R visit(GoalSpec n);

    R visit(GoalSpecs n);

    R visit(IfExThenElseTerm n);

    R visit(IfThenElseTerm n);

    R visit(ImplicationTerm n);

    R visit(IncludeStatement n);

    R visit(IntegerLiteral n);

    R visit(Invariants n);

    R visit(KeyJavaType n);

    R visit(Label n);

    R visit(LocationTerm n);

    R visit(LocsetTerm n);

    R visit(ModalityTerm n);

    R visit(Modifiers n);

    R visit(NegationTerm n);

    R visit(OneBoundVariable n);

    R visit(OneContract n);

    R visit(OneInclude n);

    R visit(OneInvariant n);

    R visit(OneOfSorts n);

    R visit(OneSchemaVarDecl n);

    R visit(OptionDecls n);

    R visit(OptionList n);

    R visit(OptionsChoice n);

    R visit(ParallelTerm n);

    R visit(PredDecl n);

    R visit(PredDecls n);

    R visit(Preferences n);

    R visit(Problem n);

    R visit(Profile n);

    R visit(ProgVarDecls n);

    R visit(Proof n);

    R visit(ProofScriptCommand n);

    R visit(ProofScriptEntry n);

    R visit(ProofScript n);

    R visit(ProofScriptParameter n);

    R visit(ProxySortDecl n);

    R visit(QuantifierTerm n);

    R visit(ReplaceWith n);

    R visit(RulesetDecl n);

    R visit(RulesetDecls n);

    R visit(RulesOrAxioms n);

    R visit(SchemaModifiers n);

    R visit(SchemaVarDecl n);

    R visit(SchemaVarDecls n);

    R visit(SemiSequent n);

    R visit(Seq n);

    R visit(SimpleIdentDots n);

    R visit(SortDecls n);

    R visit(SortId n);

    R visit(StringLiteral n);

    R visit(StrongArithTerm1 n);

    R visit(StrongArithTerm2 n);

    R visit(StubAstNodes n);

    R visit(SubstitutionTerm n);

    R visit(Taclet n);

    R visit(Term n);

    R visit(TermOrSeq n);

    R visit(TransformDecl n);

    R visit(TransformDecls n);

    R visit(Triggers n);

    R visit(UnaryMinusTerm n);

    R visit(UpdateTerm n);

    R visit(Varexp n);

    R visit(VarexpList n);

    R visit(WeakArithTerm n);

    R visit(WhereToBind n);
}
