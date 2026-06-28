package org.key_project.key.ast.visitor;

import org.key_project.key.ast.*;
import java.util.*;
import org.key_project.java.ast.*;

public interface VisitorWithDefaults<R> {

    default R visit(Abbreviation n) {
        return defaultVisit(n);
    }

    default R visit(AbstractSortDecl n) {
        return defaultVisit(n);
    }

    default R visit(AccessTerm n) {
        return defaultVisit(n);
    }

    default R visit(ActivatedChoice n) {
        return defaultVisit(n);
    }

    default R visit(Add n) {
        return defaultVisit(n);
    }

    default R visit(AddProgVars n) {
        return defaultVisit(n);
    }

    default R visit(AddRules n) {
        return defaultVisit(n);
    }

    default R visit(AliasDeclimplements n) {
        return defaultVisit(n);
    }

    default R visit(ArgSorts n) {
        return defaultVisit(n);
    }

    default R visit(ArgSortsOrFormula n) {
        return defaultVisit(n);
    }

    default R visit(Attribute n) {
        return defaultVisit(n);
    }

    default R visit(BooleanLiteral n) {
        return defaultVisit(n);
    }

    default R visit(BoundVariables n) {
        return defaultVisit(n);
    }

    default R visit(BraceSuffix n) {
        return defaultVisit(n);
    }

    default R visit(BracketSuffixHeap n) {
        return defaultVisit(n);
    }

    default R visit(BracketTerm n) {
        return defaultVisit(n);
    }

    default R visit(Call n) {
        return defaultVisit(n);
    }

    default R visit(CastTerm n) {
        return defaultVisit(n);
    }

    default R visit(CharLiteral n) {
        return defaultVisit(n);
    }

    default R visit(Choice n) {
        return defaultVisit(n);
    }

    default R visit(CKey n) {
        return defaultVisit(n);
    }

    default R visit(CKV n) {
        return defaultVisit(n);
    }

    default R visit(ComparisonTerm n) {
        return defaultVisit(n);
    }

    default R visit(ConfigurationFile n) {
        return defaultVisit(n);
    }

    default R visit(ConjunctionTerm n) {
        return defaultVisit(n);
    }

    default R visit(Contracts n) {
        return defaultVisit(n);
    }

    default R visit(CValue n) {
        return defaultVisit(n);
    }

    default R visit(DatatypeConstructor n) {
        return defaultVisit(n);
    }

    default R visit(DatatypeDecl n) {
        return defaultVisit(n);
    }

    default R visit(DatatypeDecls n) {
        return defaultVisit(n);
    }

    default R visit(DeclList n) {
        return defaultVisit(n);
    }

    default R visit(DisjunctionTerm n) {
        return defaultVisit(n);
    }

    default R visit(ElementaryUpdateTerm n) {
        return defaultVisit(n);
    }

    default R visit(EqualityTerm n) {
        return defaultVisit(n);
    }

    default R visit(EquivalenceTerm n) {
        return defaultVisit(n);
    }

    default R visit(ExtendsSorts n) {
        return defaultVisit(n);
    }

    default R visit(File n) {
        return defaultVisit(n);
    }

    default R visit(FloatLiteral n) {
        return defaultVisit(n);
    }

    default R visit(FormalSortArgs n) {
        return defaultVisit(n);
    }

    default R visit(FormalSortParamDecls n) {
        return defaultVisit(n);
    }

    default R visit(Formula n) {
        return defaultVisit(n);
    }

    default R visit(FuncDecl n) {
        return defaultVisit(n);
    }

    default R visit(FuncDecls n) {
        return defaultVisit(n);
    }

    default R visit(FuncPredName n) {
        return defaultVisit(n);
    }

    default R visit(GenericSortDecl n) {
        return defaultVisit(n);
    }

    default R visit(GoalSpec n) {
        return defaultVisit(n);
    }

    default R visit(GoalSpecs n) {
        return defaultVisit(n);
    }

    default R visit(IfExThenElseTerm n) {
        return defaultVisit(n);
    }

    default R visit(IfThenElseTerm n) {
        return defaultVisit(n);
    }

    default R visit(ImplicationTerm n) {
        return defaultVisit(n);
    }

    default R visit(IncludeStatement n) {
        return defaultVisit(n);
    }

    default R visit(IntegerLiteral n) {
        return defaultVisit(n);
    }

    default R visit(Invariants n) {
        return defaultVisit(n);
    }

    default R visit(KeyJavaType n) {
        return defaultVisit(n);
    }

    default R visit(Label n) {
        return defaultVisit(n);
    }

    default R visit(LocationTerm n) {
        return defaultVisit(n);
    }

    default R visit(LocsetTerm n) {
        return defaultVisit(n);
    }

    default R visit(ModalityTerm n) {
        return defaultVisit(n);
    }

    default R visit(Modifiers n) {
        return defaultVisit(n);
    }

    default R visit(NegationTerm n) {
        return defaultVisit(n);
    }

    default R visit(OneBoundVariable n) {
        return defaultVisit(n);
    }

    default R visit(OneContract n) {
        return defaultVisit(n);
    }

    default R visit(OneInclude n) {
        return defaultVisit(n);
    }

    default R visit(OneInvariant n) {
        return defaultVisit(n);
    }

    default R visit(OneOfSorts n) {
        return defaultVisit(n);
    }

    default R visit(OneSchemaVarDecl n) {
        return defaultVisit(n);
    }

    default R visit(OptionDecls n) {
        return defaultVisit(n);
    }

    default R visit(OptionList n) {
        return defaultVisit(n);
    }

    default R visit(OptionsChoice n) {
        return defaultVisit(n);
    }

    default R visit(ParallelTerm n) {
        return defaultVisit(n);
    }

    default R visit(PredDecl n) {
        return defaultVisit(n);
    }

    default R visit(PredDecls n) {
        return defaultVisit(n);
    }

    default R visit(Preferences n) {
        return defaultVisit(n);
    }

    default R visit(Problem n) {
        return defaultVisit(n);
    }

    default R visit(Profile n) {
        return defaultVisit(n);
    }

    default R visit(ProgVarDecls n) {
        return defaultVisit(n);
    }

    default R visit(Proof n) {
        return defaultVisit(n);
    }

    default R visit(ProofScriptCommand n) {
        return defaultVisit(n);
    }

    default R visit(ProofScriptEntry n) {
        return defaultVisit(n);
    }

    default R visit(ProofScript n) {
        return defaultVisit(n);
    }

    default R visit(ProofScriptParameter n) {
        return defaultVisit(n);
    }

    default R visit(ProxySortDecl n) {
        return defaultVisit(n);
    }

    default R visit(QuantifierTerm n) {
        return defaultVisit(n);
    }

    default R visit(ReplaceWith n) {
        return defaultVisit(n);
    }

    default R visit(RulesetDecl n) {
        return defaultVisit(n);
    }

    default R visit(RulesetDecls n) {
        return defaultVisit(n);
    }

    default R visit(RulesOrAxioms n) {
        return defaultVisit(n);
    }

    default R visit(SchemaModifiers n) {
        return defaultVisit(n);
    }

    default R visit(SchemaVarDecl n) {
        return defaultVisit(n);
    }

    default R visit(SchemaVarDecls n) {
        return defaultVisit(n);
    }

    default R visit(SemiSequent n) {
        return defaultVisit(n);
    }

    default R visit(Seq n) {
        return defaultVisit(n);
    }

    default R visit(SimpleIdentDots n) {
        return defaultVisit(n);
    }

    default R visit(SortDecls n) {
        return defaultVisit(n);
    }

    default R visit(SortId n) {
        return defaultVisit(n);
    }

    default R visit(StringLiteral n) {
        return defaultVisit(n);
    }

    default R visit(StrongArithTerm1 n) {
        return defaultVisit(n);
    }

    default R visit(StrongArithTerm2 n) {
        return defaultVisit(n);
    }

    default R visit(StubAstNodes n) {
        return defaultVisit(n);
    }

    default R visit(SubstitutionTerm n) {
        return defaultVisit(n);
    }

    default R visit(Taclet n) {
        return defaultVisit(n);
    }

    default R visit(Term n) {
        return defaultVisit(n);
    }

    default R visit(TermOrSeq n) {
        return defaultVisit(n);
    }

    default R visit(TransformDecl n) {
        return defaultVisit(n);
    }

    default R visit(TransformDecls n) {
        return defaultVisit(n);
    }

    default R visit(Triggers n) {
        return defaultVisit(n);
    }

    default R visit(UnaryMinusTerm n) {
        return defaultVisit(n);
    }

    default R visit(UpdateTerm n) {
        return defaultVisit(n);
    }

    default R visit(Varexp n) {
        return defaultVisit(n);
    }

    default R visit(VarexpList n) {
        return defaultVisit(n);
    }

    default R visit(WeakArithTerm n) {
        return defaultVisit(n);
    }

    default R visit(WhereToBind n) {
        return defaultVisit(n);
    }

    R defaultVisit(AstNode n);
}
