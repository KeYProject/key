package org.key_project.key.ast.visitor;

import org.key_project.key.ast.*;
import java.util.*;

public class CopyOnWriteVisitor implements Visitor<AstNode> {

    protected <T extends Visitable> T accept(T n) {
        return n != null ? n.accept(this) : null;
    }

    protected <T extends Visitable> List<T> accept(List<T> n) {
        return n != null ? n.stream().map(it -> (T) it.accept(this)).toList() : null;
    }

    protected <T> T accept(T n) {
        return n;
    }

    @Override()
    public org.key_project.key.ast.Abbreviation visit(Abbreviation n) {
        var b = n.builder();
        b.definition = (Term) accept(n.definition());
        b.position = (Position) accept(n.position());
        boolean clean = (n.name() == b.name) && (n.definition() == b.definition) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.AbstractSortDecl visit(AbstractSortDecl n) {
        var b = n.builder();
        b.sortIds = (List<SimpleIdentDots>) accept(n.sortIds());
        b.formalSortParamDecls = (FormalSortParamDecls) accept(n.formalSortParamDecls());
        b.extendsSorts = (ExtendsSorts) accept(n.extendsSorts());
        b.position = (Position) accept(n.position());
        boolean clean = (n.isAbstract() == b.isAbstract) && (n.sortIds() == b.sortIds) && (n.docComment() == b.docComment) && (n.formalSortParamDecls() == b.formalSortParamDecls) && (n.extendsSorts() == b.extendsSorts) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.AccessTerm visit(AccessTerm n) {
        var b = n.builder();
        b.location = (LocationTerm) accept(n.location());
        b.position = (Position) accept(n.position());
        boolean clean = (n.location() == b.location) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.ActivatedChoice visit(ActivatedChoice n) {
        var b = n.builder();
        b.position = (Position) accept(n.position());
        boolean clean = (n.category() == b.category) && (n.choice() == b.choice) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.Add visit(Add n) {
        var b = n.builder();
        b.term = (Term) accept(n.term());
        b.position = (Position) accept(n.position());
        boolean clean = (n.term() == b.term) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.AddProgVars visit(AddProgVars n) {
        var b = n.builder();
        b.type = (KeyJavaType) accept(n.type());
        b.position = (Position) accept(n.position());
        boolean clean = (n.name() == b.name) && (n.type() == b.type) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.AddRules visit(AddRules n) {
        var b = n.builder();
        b.position = (Position) accept(n.position());
        boolean clean = (n.ruleNames() == b.ruleNames) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.AliasDeclimplements visit(AliasDeclimplements n) {
        var b = n.builder();
        b.aliasName = (SimpleIdentDots) accept(n.aliasName());
        b.targetSort = (SortId) accept(n.targetSort());
        b.position = (Position) accept(n.position());
        boolean clean = (n.docComment() == b.docComment) && (n.aliasName() == b.aliasName) && (n.targetSort() == b.targetSort) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.ArgSorts visit(ArgSorts n) {
        var b = n.builder();
        b.sorts = (List<SortId>) accept(n.sorts());
        b.position = (Position) accept(n.position());
        boolean clean = (n.sorts() == b.sorts) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.ArgSortsOrFormula visit(ArgSortsOrFormula n) {
        var b = n.builder();
        b.items = (List<Object>) accept(n.items());
        b.position = (Position) accept(n.position());
        boolean clean = (n.items() == b.items) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.Attribute visit(Attribute n) {
        var b = n.builder();
        b.position = (Position) accept(n.position());
        boolean clean = (n.fieldName() == b.fieldName) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.BooleanLiteral visit(BooleanLiteral n) {
        var b = n.builder();
        b.position = (Position) accept(n.position());
        boolean clean = (n.value() == b.value) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.BoundVariables visit(BoundVariables n) {
        var b = n.builder();
        b.variables = (List<OneBoundVariable>) accept(n.variables());
        b.position = (Position) accept(n.position());
        boolean clean = (n.variables() == b.variables) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.BraceSuffix visit(BraceSuffix n) {
        var b = n.builder();
        b.elements = (java.util.List<Term>) accept(n.elements());
        b.position = (Position) accept(n.position());
        boolean clean = (n.elements() == b.elements) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.BracketSuffixHeap visit(BracketSuffixHeap n) {
        var b = n.builder();
        b.indices = (java.util.List<Term>) accept(n.indices());
        b.position = (Position) accept(n.position());
        boolean clean = (n.indices() == b.indices) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.BracketTerm visit(BracketTerm n) {
        var b = n.builder();
        b.inner = (Term) accept(n.inner());
        b.suffix = (BracketSuffixHeap) accept(n.suffix());
        b.position = (Position) accept(n.position());
        boolean clean = (n.inner() == b.inner) && (n.suffix() == b.suffix) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.Call visit(Call n) {
        var b = n.builder();
        b.arguments = (java.util.List<Term>) accept(n.arguments());
        b.position = (Position) accept(n.position());
        boolean clean = (n.arguments() == b.arguments) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.CastTerm visit(CastTerm n) {
        var b = n.builder();
        b.targetType = (SortId) accept(n.targetType());
        b.operand = (Term) accept(n.operand());
        b.position = (Position) accept(n.position());
        boolean clean = (n.targetType() == b.targetType) && (n.operand() == b.operand) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.CharLiteral visit(CharLiteral n) {
        var b = n.builder();
        b.position = (Position) accept(n.position());
        boolean clean = (n.value() == b.value) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.Choice visit(Choice n) {
        var b = n.builder();
        b.position = (Position) accept(n.position());
        boolean clean = (n.docComments() == b.docComments) && (n.category() == b.category) && (n.optionDecls() == b.optionDecls) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.CKey visit(CKey n) {
        var b = n.builder();
        b.position = (Position) accept(n.position());
        boolean clean = (n.key() == b.key) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.CKV visit(CKV n) {
        var b = n.builder();
        b.key = (CKey) accept(n.key());
        b.value = (CValue) accept(n.value());
        b.position = (Position) accept(n.position());
        boolean clean = (n.key() == b.key) && (n.value() == b.value) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.ComparisonTerm visit(ComparisonTerm n) {
        var b = n.builder();
        b.left = (Term) accept(n.left());
        b.right = (Term) accept(n.right());
        b.operator = (Op) accept(n.operator());
        b.position = (Position) accept(n.position());
        boolean clean = (n.left() == b.left) && (n.right() == b.right) && (n.operator() == b.operator) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.ConfigurationFile visit(ConfigurationFile n) {
        var b = n.builder();
        b.entries = (List<CKV>) accept(n.entries());
        b.position = (Position) accept(n.position());
        boolean clean = (n.entries() == b.entries) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.ConjunctionTerm visit(ConjunctionTerm n) {
        var b = n.builder();
        b.left = (Term) accept(n.left());
        b.right = (Term) accept(n.right());
        b.position = (Position) accept(n.position());
        boolean clean = (n.left() == b.left) && (n.right() == b.right) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.Contracts visit(Contracts n) {
        var b = n.builder();
        b.items = (List<RulesOrAxioms>) accept(n.items());
        b.position = (Position) accept(n.position());
        boolean clean = (n.items() == b.items) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.CValue visit(CValue n) {
        var b = n.builder();
        b.position = (Position) accept(n.position());
        boolean clean = (n.value() == b.value) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.DatatypeConstructor visit(DatatypeConstructor n) {
        var b = n.builder();
        b.name = (SimpleIdentDots) accept(n.name());
        b.argSorts = (ArgSorts) accept(n.argSorts());
        b.position = (Position) accept(n.position());
        boolean clean = (n.name() == b.name) && (n.argSorts() == b.argSorts) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.DatatypeDecl visit(DatatypeDecl n) {
        var b = n.builder();
        b.name = (SimpleIdentDots) accept(n.name());
        b.formalSortParams = (FormalSortParamDecls) accept(n.formalSortParams());
        b.constructors = (List<DatatypeConstructor>) accept(n.constructors());
        b.position = (Position) accept(n.position());
        boolean clean = (n.docComment() == b.docComment) && (n.isFree() == b.isFree) && (n.name() == b.name) && (n.formalSortParams() == b.formalSortParams) && (n.constructors() == b.constructors) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.DatatypeDecls visit(DatatypeDecls n) {
        var b = n.builder();
        b.decls = (List<DatatypeDecl>) accept(n.decls());
        b.position = (Position) accept(n.position());
        boolean clean = (n.decls() == b.decls) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.DeclList visit(DeclList n) {
        var b = n.builder();
        b.declarations = (List<Declaration>) accept(n.declarations());
        b.position = (Position) accept(n.position());
        boolean clean = (n.declarations() == b.declarations) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.DisjunctionTerm visit(DisjunctionTerm n) {
        var b = n.builder();
        b.left = (Term) accept(n.left());
        b.right = (Term) accept(n.right());
        b.position = (Position) accept(n.position());
        boolean clean = (n.left() == b.left) && (n.right() == b.right) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.ElementaryUpdateTerm visit(ElementaryUpdateTerm n) {
        var b = n.builder();
        b.location = (LocationTerm) accept(n.location());
        b.value = (Term) accept(n.value());
        b.position = (Position) accept(n.position());
        boolean clean = (n.location() == b.location) && (n.value() == b.value) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.EqualityTerm visit(EqualityTerm n) {
        var b = n.builder();
        b.left = (Term) accept(n.left());
        b.right = (Term) accept(n.right());
        b.position = (Position) accept(n.position());
        boolean clean = (n.left() == b.left) && (n.right() == b.right) && (n.isEquality() == b.isEquality) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.EquivalenceTerm visit(EquivalenceTerm n) {
        var b = n.builder();
        b.left = (Term) accept(n.left());
        b.right = (Term) accept(n.right());
        b.position = (Position) accept(n.position());
        boolean clean = (n.left() == b.left) && (n.right() == b.right) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.ExtendsSorts visit(ExtendsSorts n) {
        var b = n.builder();
        b.sortIds = (List<SortId>) accept(n.sortIds());
        b.position = (Position) accept(n.position());
        boolean clean = (n.sortIds() == b.sortIds) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.File visit(File n) {
        var b = n.builder();
        b.profile = (Profile) accept(n.profile());
        b.preferences = (Preferences) accept(n.preferences());
        b.decls = (DeclList) accept(n.decls());
        b.problem = (Problem) accept(n.problem());
        b.proof = (Proof) accept(n.proof());
        b.position = (Position) accept(n.position());
        boolean clean = (n.docComments() == b.docComments) && (n.profile() == b.profile) && (n.preferences() == b.preferences) && (n.decls() == b.decls) && (n.problem() == b.problem) && (n.proof() == b.proof) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.FloatLiteral visit(FloatLiteral n) {
        var b = n.builder();
        b.position = (Position) accept(n.position());
        boolean clean = (n.value() == b.value) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.FormalSortArgs visit(FormalSortArgs n) {
        var b = n.builder();
        b.sortIds = (List<SortId>) accept(n.sortIds());
        b.position = (Position) accept(n.position());
        boolean clean = (n.sortIds() == b.sortIds) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.FormalSortParamDecls visit(FormalSortParamDecls n) {
        var b = n.builder();
        b.sortIds = (List<SortId>) accept(n.sortIds());
        b.position = (Position) accept(n.position());
        boolean clean = (n.sortIds() == b.sortIds) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.Formula visit(Formula n) {
        var b = n.builder();
        b.term = (Term) accept(n.term());
        b.position = (Position) accept(n.position());
        boolean clean = (n.term() == b.term) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.FuncDecl visit(FuncDecl n) {
        var b = n.builder();
        b.returnSort = (SortId) accept(n.returnSort());
        b.name = (FuncPredName) accept(n.name());
        b.formalSortParams = (FormalSortParamDecls) accept(n.formalSortParams());
        b.whereToBind = (WhereToBind) accept(n.whereToBind());
        b.argSorts = (ArgSorts) accept(n.argSorts());
        b.position = (Position) accept(n.position());
        boolean clean = (n.docComment() == b.docComment) && (n.isUnique() == b.isUnique) && (n.returnSort() == b.returnSort) && (n.name() == b.name) && (n.formalSortParams() == b.formalSortParams) && (n.whereToBind() == b.whereToBind) && (n.argSorts() == b.argSorts) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.FuncDecls visit(FuncDecls n) {
        var b = n.builder();
        b.decls = (List<FuncDecl>) accept(n.decls());
        b.position = (Position) accept(n.position());
        boolean clean = (n.decls() == b.decls) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.FuncPredName visit(FuncPredName n) {
        var b = n.builder();
        b.sortPrefix = (SortId) accept(n.sortPrefix());
        b.name = (SimpleIdentDots) accept(n.name());
        b.position = (Position) accept(n.position());
        boolean clean = (n.sortPrefix() == b.sortPrefix) && (n.name() == b.name) && (n.intLiteral() == b.intLiteral) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.GenericSortDecl visit(GenericSortDecl n) {
        var b = n.builder();
        b.extendsSorts = (ExtendsSorts) accept(n.extendsSorts());
        b.formalParams = (FormalSortParamDecls) accept(n.formalParams());
        b.position = (Position) accept(n.position());
        boolean clean = (n.docComment() == b.docComment) && (n.sortNames() == b.sortNames) && (n.extendsSorts() == b.extendsSorts) && (n.formalParams() == b.formalParams) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.GoalSpec visit(GoalSpec n) {
        var b = n.builder();
        b.termOrSeq = (TermOrSeq) accept(n.termOrSeq());
        b.position = (Position) accept(n.position());
        boolean clean = (n.termOrSeq() == b.termOrSeq) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.GoalSpecs visit(GoalSpecs n) {
        var b = n.builder();
        b.specs = (List<GoalSpec>) accept(n.specs());
        b.position = (Position) accept(n.position());
        boolean clean = (n.specs() == b.specs) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.IfExThenElseTerm visit(IfExThenElseTerm n) {
        var b = n.builder();
        b.condition = (Term) accept(n.condition());
        b.thenBranch = (Term) accept(n.thenBranch());
        b.elseBranch = (Term) accept(n.elseBranch());
        b.position = (Position) accept(n.position());
        boolean clean = (n.condition() == b.condition) && (n.thenBranch() == b.thenBranch) && (n.elseBranch() == b.elseBranch) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.IfThenElseTerm visit(IfThenElseTerm n) {
        var b = n.builder();
        b.condition = (Term) accept(n.condition());
        b.thenBranch = (Term) accept(n.thenBranch());
        b.elseBranch = (Term) accept(n.elseBranch());
        b.position = (Position) accept(n.position());
        boolean clean = (n.condition() == b.condition) && (n.thenBranch() == b.thenBranch) && (n.elseBranch() == b.elseBranch) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.ImplicationTerm visit(ImplicationTerm n) {
        var b = n.builder();
        b.left = (Term) accept(n.left());
        b.right = (Term) accept(n.right());
        b.position = (Position) accept(n.position());
        boolean clean = (n.left() == b.left) && (n.right() == b.right) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.IncludeStatement visit(IncludeStatement n) {
        var b = n.builder();
        b.includes = (List<OneInclude>) accept(n.includes());
        b.position = (Position) accept(n.position());
        boolean clean = (n.isLdt() == b.isLdt) && (n.includes() == b.includes) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.IntegerLiteral visit(IntegerLiteral n) {
        var b = n.builder();
        b.position = (Position) accept(n.position());
        boolean clean = (n.value() == b.value) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.Invariants visit(Invariants n) {
        var b = n.builder();
        b.items = (List<RulesOrAxioms>) accept(n.items());
        b.position = (Position) accept(n.position());
        boolean clean = (n.items() == b.items) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.KeyJavaType visit(KeyJavaType n) {
        var b = n.builder();
        b.position = (Position) accept(n.position());
        boolean clean = (n.typeName() == b.typeName) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.Label visit(Label n) {
        var b = n.builder();
        b.position = (Position) accept(n.position());
        boolean clean = (n.name() == b.name) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.LocationTerm visit(LocationTerm n) {
        var b = n.builder();
        b.qualifier = (Term) accept(n.qualifier());
        b.arrayIndices = (java.util.List<Term>) accept(n.arrayIndices());
        b.position = (Position) accept(n.position());
        boolean clean = (n.baseName() == b.baseName) && (n.qualifier() == b.qualifier) && (n.fieldChain() == b.fieldChain) && (n.arrayIndices() == b.arrayIndices) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.LocsetTerm visit(LocsetTerm n) {
        var b = n.builder();
        b.locations = (List<Term>) accept(n.locations());
        b.position = (Position) accept(n.position());
        boolean clean = (n.locations() == b.locations) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.ModalityTerm visit(ModalityTerm n) {
        var b = n.builder();
        b.program = (Term) accept(n.program());
        b.body = (Term) accept(n.body());
        b.position = (Position) accept(n.position());
        boolean clean = (n.isBox() == b.isBox) && (n.program() == b.program) && (n.body() == b.body) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.Modifiers visit(Modifiers n) {
        var b = n.builder();
        b.position = (Position) accept(n.position());
        boolean clean = (n.modifierNames() == b.modifierNames) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.NegationTerm visit(NegationTerm n) {
        var b = n.builder();
        b.operand = (Term) accept(n.operand());
        b.position = (Position) accept(n.position());
        boolean clean = (n.operand() == b.operand) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.OneBoundVariable visit(OneBoundVariable n) {
        var b = n.builder();
        b.sort = (SortId) accept(n.sort());
        b.position = (Position) accept(n.position());
        boolean clean = (n.sort() == b.sort) && (n.name() == b.name) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.OneContract visit(OneContract n) {
        var b = n.builder();
        b.formula = (Term) accept(n.formula());
        b.modifiableClause = (Term) accept(n.modifiableClause());
        b.position = (Position) accept(n.position());
        boolean clean = (n.name() == b.name) && (n.formula() == b.formula) && (n.modifiableClause() == b.modifiableClause) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.OneInclude visit(OneInclude n) {
        var b = n.builder();
        b.position = (Position) accept(n.position());
        boolean clean = (n.value() == b.value) && (n.isAbsolute() == b.isAbsolute) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.OneInvariant visit(OneInvariant n) {
        var b = n.builder();
        b.formula = (Term) accept(n.formula());
        b.position = (Position) accept(n.position());
        boolean clean = (n.name() == b.name) && (n.formula() == b.formula) && (n.displayName() == b.displayName) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.OneOfSorts visit(OneOfSorts n) {
        var b = n.builder();
        b.sortIds = (List<SortId>) accept(n.sortIds());
        b.position = (Position) accept(n.position());
        boolean clean = (n.sortIds() == b.sortIds) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.OneSchemaVarDecl visit(OneSchemaVarDecl n) {
        var b = n.builder();
        b.modifiers = (SchemaModifiers) accept(n.modifiers());
        b.sortId = (SortId) accept(n.sortId());
        b.parameter = (SimpleIdentDots) accept(n.parameter());
        b.modalOpSort = (SortId) accept(n.modalOpSort());
        b.position = (Position) accept(n.position());
        boolean clean = (n.kind() == b.kind) && (n.modifiers() == b.modifiers) && (n.sortId() == b.sortId) && (n.nameString() == b.nameString) && (n.parameter() == b.parameter) && (n.identifiers() == b.identifiers) && (n.modalOpName() == b.modalOpName) && (n.modalOpSort() == b.modalOpSort) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.OptionDecls visit(OptionDecls n) {
        var b = n.builder();
        b.choices = (List<Choice>) accept(n.choices());
        b.position = (Position) accept(n.position());
        boolean clean = (n.choices() == b.choices) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.OptionList visit(OptionList n) {
        var b = n.builder();
        b.options = (List<OptionExpr>) accept(n.options());
        b.position = (Position) accept(n.position());
        boolean clean = (n.options() == b.options) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.OptionsChoice visit(OptionsChoice n) {
        var b = n.builder();
        b.choices = (List<ActivatedChoice>) accept(n.choices());
        b.position = (Position) accept(n.position());
        boolean clean = (n.choices() == b.choices) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.ParallelTerm visit(ParallelTerm n) {
        var b = n.builder();
        b.updates = (List<ElementaryUpdateTerm>) accept(n.updates());
        b.position = (Position) accept(n.position());
        boolean clean = (n.updates() == b.updates) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.PredDecl visit(PredDecl n) {
        var b = n.builder();
        b.name = (FuncPredName) accept(n.name());
        b.formalSortParams = (FormalSortParamDecls) accept(n.formalSortParams());
        b.whereToBind = (WhereToBind) accept(n.whereToBind());
        b.argSorts = (ArgSorts) accept(n.argSorts());
        b.position = (Position) accept(n.position());
        boolean clean = (n.docComment() == b.docComment) && (n.name() == b.name) && (n.formalSortParams() == b.formalSortParams) && (n.whereToBind() == b.whereToBind) && (n.argSorts() == b.argSorts) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.PredDecls visit(PredDecls n) {
        var b = n.builder();
        b.decls = (List<PredDecl>) accept(n.decls());
        b.position = (Position) accept(n.position());
        boolean clean = (n.decls() == b.decls) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.Preferences visit(Preferences n) {
        var b = n.builder();
        b.cvalue = (CValue) accept(n.cvalue());
        b.position = (Position) accept(n.position());
        boolean clean = (n.stringValue() == b.stringValue) && (n.cvalue() == b.cvalue) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.Problem visit(Problem n) {
        var b = n.builder();
        b.termOrSeq = (Term) accept(n.termOrSeq());
        b.proofScriptEntry = (ProofScriptEntry) accept(n.proofScriptEntry());
        b.position = (Position) accept(n.position());
        boolean clean = (n.termOrSeq() == b.termOrSeq) && (n.chooseContract() == b.chooseContract) && (n.proofObligation() == b.proofObligation) && (n.proofScriptEntry() == b.proofScriptEntry) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.Profile visit(Profile n) {
        var b = n.builder();
        b.position = (Position) accept(n.position());
        boolean clean = (n.name() == b.name) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.ProgVarDecls visit(ProgVarDecls n) {
        var b = n.builder();
        b.types = (List<KeyJavaType>) accept(n.types());
        b.position = (Position) accept(n.position());
        boolean clean = (n.types() == b.types) && (n.varNames() == b.varNames) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.Proof visit(Proof n) {
        var b = n.builder();
        b.position = (Position) accept(n.position());
        boolean clean = (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.ProofScriptCommand visit(ProofScriptCommand n) {
        var b = n.builder();
        b.position = (Position) accept(n.position());
        boolean clean = (n.name() == b.name) && (n.arguments() == b.arguments) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.ProofScriptEntry visit(ProofScriptEntry n) {
        var b = n.builder();
        b.inlineScript = (ProofScript) accept(n.inlineScript());
        b.position = (Position) accept(n.position());
        boolean clean = (n.scriptPath() == b.scriptPath) && (n.inlineScript() == b.inlineScript) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.ProofScript visit(ProofScript n) {
        var b = n.builder();
        b.commands = (List<ProofScriptCommand>) accept(n.commands());
        b.position = (Position) accept(n.position());
        boolean clean = (n.commands() == b.commands) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.ProofScriptParameter visit(ProofScriptParameter n) {
        var b = n.builder();
        b.expression = (Object) accept(n.expression());
        b.position = (Position) accept(n.position());
        boolean clean = (n.name() == b.name) && (n.expression() == b.expression) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.ProxySortDecl visit(ProxySortDecl n) {
        var b = n.builder();
        b.javaType = (KeyJavaType) accept(n.javaType());
        b.position = (Position) accept(n.position());
        boolean clean = (n.docComment() == b.docComment) && (n.sortNames() == b.sortNames) && (n.javaType() == b.javaType) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.QuantifierTerm visit(QuantifierTerm n) {
        var b = n.builder();
        b.variables = (BoundVariables) accept(n.variables());
        b.body = (Term) accept(n.body());
        b.position = (Position) accept(n.position());
        boolean clean = (n.isUniversal() == b.isUniversal) && (n.variables() == b.variables) && (n.body() == b.body) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.ReplaceWith visit(ReplaceWith n) {
        var b = n.builder();
        b.term = (Term) accept(n.term());
        b.antecedent = (Seq) accept(n.antecedent());
        b.succulent = (Seq) accept(n.succulent());
        b.position = (Position) accept(n.position());
        boolean clean = (n.term() == b.term) && (n.antecedent() == b.antecedent) && (n.succulent() == b.succulent) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.RulesetDecl visit(RulesetDecl n) {
        var b = n.builder();
        b.name = (SimpleIdentDots) accept(n.name());
        b.parentRules = (List<SimpleIdentDots>) accept(n.parentRules());
        b.position = (Position) accept(n.position());
        boolean clean = (n.docComment() == b.docComment) && (n.name() == b.name) && (n.parentRules() == b.parentRules) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.RulesetDecls visit(RulesetDecls n) {
        var b = n.builder();
        b.decls = (List<RulesetDecl>) accept(n.decls());
        b.position = (Position) accept(n.position());
        boolean clean = (n.decls() == b.decls) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.RulesOrAxioms visit(RulesOrAxioms n) {
        var b = n.builder();
        b.condition = (Term) accept(n.condition());
        b.formula = (Formula) accept(n.formula());
        b.whenCondition = (Formula) accept(n.whenCondition());
        b.position = (Position) accept(n.position());
        boolean clean = (n.name() == b.name) && (n.condition() == b.condition) && (n.isAxiom() == b.isAxiom) && (n.formula() == b.formula) && (n.whenCondition() == b.whenCondition) && (n.rulesetNames() == b.rulesetNames) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.SchemaModifiers visit(SchemaModifiers n) {
        var b = n.builder();
        b.position = (Position) accept(n.position());
        boolean clean = (n.options() == b.options) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.SchemaVarDecl visit(SchemaVarDecl n) {
        var b = n.builder();
        b.position = (Position) accept(n.position());
        boolean clean = (n.name() == b.name) && (n.kind() == b.kind) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.SchemaVarDecls visit(SchemaVarDecls n) {
        var b = n.builder();
        b.decls = (List<OneSchemaVarDecl>) accept(n.decls());
        b.position = (Position) accept(n.position());
        boolean clean = (n.decls() == b.decls) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.SemiSequent visit(SemiSequent n) {
        var b = n.builder();
        b.antecedent = (Seq) accept(n.antecedent());
        b.succulent = (Seq) accept(n.succulent());
        b.position = (Position) accept(n.position());
        boolean clean = (n.antecedent() == b.antecedent) && (n.succulent() == b.succulent) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.Seq visit(Seq n) {
        var b = n.builder();
        b.terms = (List<Term>) accept(n.terms());
        b.position = (Position) accept(n.position());
        boolean clean = (n.terms() == b.terms) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.SimpleIdentDots visit(SimpleIdentDots n) {
        var b = n.builder();
        b.position = (Position) accept(n.position());
        boolean clean = (n.fullName() == b.fullName) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.SortDecls visit(SortDecls n) {
        var b = n.builder();
        b.sortDecls = (List<OneSortDecl>) accept(n.sortDecls());
        b.position = (Position) accept(n.position());
        boolean clean = (n.sortDecls() == b.sortDecls) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.SortId visit(SortId n) {
        var b = n.builder();
        b.formalArgs = (FormalSortArgs) accept(n.formalArgs());
        b.position = (Position) accept(n.position());
        boolean clean = (n.parts() == b.parts) && (n.formalArgs() == b.formalArgs) && (n.arrayDimensions() == b.arrayDimensions) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.StringLiteral visit(StringLiteral n) {
        var b = n.builder();
        b.position = (Position) accept(n.position());
        boolean clean = (n.value() == b.value) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.StrongArithTerm1 visit(StrongArithTerm1 n) {
        var b = n.builder();
        b.operand = (Term) accept(n.operand());
        b.operator = (Op) accept(n.operator());
        b.position = (Position) accept(n.position());
        boolean clean = (n.operand() == b.operand) && (n.operator() == b.operator) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.StrongArithTerm2 visit(StrongArithTerm2 n) {
        var b = n.builder();
        b.left = (Term) accept(n.left());
        b.right = (Term) accept(n.right());
        b.operator = (Op) accept(n.operator());
        b.position = (Position) accept(n.position());
        boolean clean = (n.left() == b.left) && (n.right() == b.right) && (n.operator() == b.operator) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.StubAstNodes visit(StubAstNodes n) {
        var b = n.builder();
        b.position = (Position) accept(n.position());
        boolean clean = (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.SubstitutionTerm visit(SubstitutionTerm n) {
        var b = n.builder();
        b.term = (Term) accept(n.term());
        b.substitution = (Term) accept(n.substitution());
        b.position = (Position) accept(n.position());
        boolean clean = (n.term() == b.term) && (n.substitution() == b.substitution) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.Taclet visit(Taclet n) {
        var b = n.builder();
        b.options = (OptionList) accept(n.options());
        b.schemaVars = (List<SchemaVarDecl>) accept(n.schemaVars());
        b.assumes = (Seq) accept(n.assumes());
        b.find = (TermOrSeq) accept(n.find());
        b.varConds = (List<VarexpList>) accept(n.varConds());
        b.goalSpecs = (GoalSpecs) accept(n.goalSpecs());
        b.modifiers = (Modifiers) accept(n.modifiers());
        b.position = (Position) accept(n.position());
        boolean clean = (n.docComment() == b.docComment) && (n.isLemma() == b.isLemma) && (n.name() == b.name) && (n.options() == b.options) && (n.schemaVars() == b.schemaVars) && (n.assumes() == b.assumes) && (n.find() == b.find) && (n.findModifiers() == b.findModifiers) && (n.varConds() == b.varConds) && (n.goalSpecs() == b.goalSpecs) && (n.modifiers() == b.modifiers) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.Term visit(Term n) {
        var b = n.builder();
        b.type = (TermType) accept(n.type());
        b.left = (Term) accept(n.left());
        b.right = (Term) accept(n.right());
        b.boundVariables = (BoundVariables) accept(n.boundVariables());
        b.label = (Label) accept(n.label());
        b.position = (Position) accept(n.position());
        boolean clean = (n.type() == b.type) && (n.operator() == b.operator) && (n.left() == b.left) && (n.right() == b.right) && (n.children() == b.children) && (n.boundVariables() == b.boundVariables) && (n.label() == b.label) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.TermOrSeq visit(TermOrSeq n) {
        var b = n.builder();
        b.term = (Term) accept(n.term());
        b.antecedent = (Seq) accept(n.antecedent());
        b.succulent = (Seq) accept(n.succulent());
        b.position = (Position) accept(n.position());
        boolean clean = (n.term() == b.term) && (n.antecedent() == b.antecedent) && (n.succulent() == b.succulent) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.TransformDecl visit(TransformDecl n) {
        var b = n.builder();
        b.returnSort = (SortId) accept(n.returnSort());
        b.name = (FuncPredName) accept(n.name());
        b.argSorts = (ArgSortsOrFormula) accept(n.argSorts());
        b.position = (Position) accept(n.position());
        boolean clean = (n.docComment() == b.docComment) && (n.returnSort() == b.returnSort) && (n.isFormula() == b.isFormula) && (n.name() == b.name) && (n.argSorts() == b.argSorts) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.TransformDecls visit(TransformDecls n) {
        var b = n.builder();
        b.decls = (List<TransformDecl>) accept(n.decls());
        b.position = (Position) accept(n.position());
        boolean clean = (n.decls() == b.decls) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.Triggers visit(Triggers n) {
        var b = n.builder();
        b.terms = (List<Term>) accept(n.terms());
        b.position = (Position) accept(n.position());
        boolean clean = (n.terms() == b.terms) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.UnaryMinusTerm visit(UnaryMinusTerm n) {
        var b = n.builder();
        b.operand = (Term) accept(n.operand());
        b.position = (Position) accept(n.position());
        boolean clean = (n.operand() == b.operand) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.UpdateTerm visit(UpdateTerm n) {
        var b = n.builder();
        b.updates = (java.util.List<ElementaryUpdateTerm>) accept(n.updates());
        b.position = (Position) accept(n.position());
        boolean clean = (n.updates() == b.updates) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.Varexp visit(Varexp n) {
        var b = n.builder();
        b.type = (KeyJavaType) accept(n.type());
        b.position = (Position) accept(n.position());
        boolean clean = (n.name() == b.name) && (n.type() == b.type) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.VarexpList visit(VarexpList n) {
        var b = n.builder();
        b.items = (List<Varexp>) accept(n.items());
        b.position = (Position) accept(n.position());
        boolean clean = (n.items() == b.items) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.WeakArithTerm visit(WeakArithTerm n) {
        var b = n.builder();
        b.left = (Term) accept(n.left());
        b.right = (Term) accept(n.right());
        b.operator = (Op) accept(n.operator());
        b.position = (Position) accept(n.position());
        boolean clean = (n.left() == b.left) && (n.right() == b.right) && (n.operator() == b.operator) && (n.position() == b.position);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.key.ast.WhereToBind visit(WhereToBind n) {
        var b = n.builder();
        b.position = (Position) accept(n.position());
        boolean clean = (n.bindValues() == b.bindValues) && (n.position() == b.position);
        return clean ? n : b.build();
    }
}
