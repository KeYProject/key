package org.key_project.key.ast.visitor;

import org.key_project.key.ast.*;
import java.util.*;

public interface VoidVisitor {

    void visit(Abbreviation n);

    void visit(AbstractSortDecl n);

    void visit(AccessTerm n);

    void visit(ActivatedChoice n);

    void visit(Add n);

    void visit(AddProgVars n);

    void visit(AddRules n);

    void visit(AliasDeclimplements n);

    void visit(ArgSorts n);

    void visit(ArgSortsOrFormula n);

    void visit(Attribute n);

    void visit(BooleanLiteral n);

    void visit(BoundVariables n);

    void visit(BraceSuffix n);

    void visit(BracketSuffixHeap n);

    void visit(BracketTerm n);

    void visit(Call n);

    void visit(CastTerm n);

    void visit(CharLiteral n);

    void visit(Choice n);

    void visit(CKey n);

    void visit(CKV n);

    void visit(ComparisonTerm n);

    void visit(ConfigurationFile n);

    void visit(ConjunctionTerm n);

    void visit(Contracts n);

    void visit(CValue n);

    void visit(DatatypeConstructor n);

    void visit(DatatypeDecl n);

    void visit(DatatypeDecls n);

    void visit(DeclList n);

    void visit(DisjunctionTerm n);

    void visit(ElementaryUpdateTerm n);

    void visit(EqualityTerm n);

    void visit(EquivalenceTerm n);

    void visit(ExtendsSorts n);

    void visit(File n);

    void visit(FloatLiteral n);

    void visit(FormalSortArgs n);

    void visit(FormalSortParamDecls n);

    void visit(Formula n);

    void visit(FuncDecl n);

    void visit(FuncDecls n);

    void visit(FuncPredName n);

    void visit(GenericSortDecl n);

    void visit(GoalSpec n);

    void visit(GoalSpecs n);

    void visit(IfExThenElseTerm n);

    void visit(IfThenElseTerm n);

    void visit(ImplicationTerm n);

    void visit(IncludeStatement n);

    void visit(IntegerLiteral n);

    void visit(Invariants n);

    void visit(KeyJavaType n);

    void visit(Label n);

    void visit(LocationTerm n);

    void visit(LocsetTerm n);

    void visit(ModalityTerm n);

    void visit(Modifiers n);

    void visit(NegationTerm n);

    void visit(OneBoundVariable n);

    void visit(OneContract n);

    void visit(OneInclude n);

    void visit(OneInvariant n);

    void visit(OneOfSorts n);

    void visit(OneSchemaVarDecl n);

    void visit(OptionDecls n);

    void visit(OptionList n);

    void visit(OptionsChoice n);

    void visit(ParallelTerm n);

    void visit(PredDecl n);

    void visit(PredDecls n);

    void visit(Preferences n);

    void visit(Problem n);

    void visit(Profile n);

    void visit(ProgVarDecls n);

    void visit(Proof n);

    void visit(ProofScriptCommand n);

    void visit(ProofScriptEntry n);

    void visit(ProofScript n);

    void visit(ProofScriptParameter n);

    void visit(ProxySortDecl n);

    void visit(QuantifierTerm n);

    void visit(ReplaceWith n);

    void visit(RulesetDecl n);

    void visit(RulesetDecls n);

    void visit(RulesOrAxioms n);

    void visit(SchemaModifiers n);

    void visit(SchemaVarDecl n);

    void visit(SchemaVarDecls n);

    void visit(SemiSequent n);

    void visit(Seq n);

    void visit(SimpleIdentDots n);

    void visit(SortDecls n);

    void visit(SortId n);

    void visit(StringLiteral n);

    void visit(StrongArithTerm1 n);

    void visit(StrongArithTerm2 n);

    void visit(StubAstNodes n);

    void visit(SubstitutionTerm n);

    void visit(Taclet n);

    void visit(Term n);

    void visit(TermOrSeq n);

    void visit(TransformDecl n);

    void visit(TransformDecls n);

    void visit(Triggers n);

    void visit(UnaryMinusTerm n);

    void visit(UpdateTerm n);

    void visit(Varexp n);

    void visit(VarexpList n);

    void visit(WeakArithTerm n);

    void visit(WhereToBind n);
}
