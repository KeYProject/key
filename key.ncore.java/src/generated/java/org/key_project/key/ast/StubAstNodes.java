package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class StubAstNodes extends BaseAstNode {

    static class IncludeStatement {

        boolean isLDTs;

        List<OneInclude> includes;
    }

    static class OneInclude {

        @Nullable
        String absFile;

        @Nullable
        String relFile;
    }

    static class OptionsChoice {

        List<ActivatedChoice> choices;
    }

    static class ActivatedChoice {

        String category;

        String choice;
    }

    static class OptionDecls {

        List<Choice> choices;
    }

    static class Choice {

        List<String> docComments;

        String category;

        List<OptionDecl> options;
    }

    static class OptionDecl {

        @Nullable
        String docComment;

        List<String> choices;
    }

    static class SortDecls {

        List<OneSortDecl> sorts;
    }

    static class OneSortDecl {

        enum SortKind {

            GENERIC, PROXY, ABSTRACT, ALIAS
        }

        SortKind kind;

        @Nullable
        String docComment;

        List<String> sortIds;

        @Nullable
        String extendsSorts;

        @Nullable
        String aliasTarget;
    }

    static class ProgVarDecls {

        List<ProgVarDecl> variables;
    }

    static class ProgVarDecl {

        String type;

        List<String> names;
    }

    static class SchemaVarDecls {

        List<OneSchemaVarDecl> schemaVars;
    }

    static class OneSchemaVarDecl {

        enum SchemaKind {

            MODAL_OPERATOR,
            PROGRAM,
            FORMULA,
            TERMLABEL,
            UPDATE,
            SKOLEM_FORMULA,
            TERM_VAR
        }

        SchemaKind kind;

        String name;

        @Nullable
        SortId sort;
    }

    static class SchemaModifiers {

        List<String> options;
    }

    static class PredDecls {

        List<PredDecl> predicates;
    }

    static class PredDecl {

        @Nullable
        String docComment;

        String name;

        List<SortId> argSorts;
    }

    static class FuncDecls {

        List<FuncDecl> functions;
    }

    static class FuncDecl {

        @Nullable
        String docComment;

        boolean unique;

        SortId returnType;

        String name;

        List<SortId> argSorts;
    }

    static class TransformDecls {

        List<TransformDecl> transforms;
    }

    static class TransformDecl {

        @Nullable
        String docComment;

        @Nullable
        SortId returnType;

        boolean returnsFormula;

        String name;

        List<Object> argSorts;

        boolean returnsFormula() {
            return returnsFormula;
        }
    }

    static class DatatypeDecls {

        List<DatatypeDecl> datatypes;
    }

    static class DatatypeDecl {

        @Nullable
        String docComment;

        String name;

        List<DatatypeConstructor> constructors;
    }

    static class DatatypeConstructor {

        String name;

        List<String> argSorts;

        List<String> argNames;
    }

    static class RulesetDecls {

        List<String> rulesets;
    }

    static class Contracts {

        List<OneContract> contracts;
    }

    static class Invariants {

        OneBoundVariable selfVar;

        List<OneInvariant> invariants;
    }

    static class RulesOrAxioms {

        @Nullable
        String docComment;

        boolean isRules;

        @Nullable
        OptionList options;

        List<Taclet> taclets;
    }

    static class OptionExpr {

        enum OpKind {

            AND, OR, NOT, PROP
        }

        OpKind kind;

        @Nullable
        OptionExpr left;

        @Nullable
        OptionExpr right;

        @Nullable
        String propCategory;

        @Nullable
        String propValue;
    }

    static class Seq {

        SemiSequent antecedent;

        SemiSequent succedent;
    }

    static class TermOrSeq {

        @Nullable
        Term term;

        @Nullable
        Seq seq;
    }

    static class SemiSequent {

        List<Term> terms;
    }

    static class GoalSpecs {

        boolean closeGoal;

        List<GoalSpecWithOption> specs;
    }

    static class GoalSpecWithOption {

        @Nullable
        OptionList options;

        GoalSpec spec;
    }

    static class GoalSpec {

        @Nullable
        String name;

        @Nullable
        String tag;

        @Nullable
        ReplaceWith replaceWith;

        @Nullable
        Add add;

        @Nullable
        AddRules addRules;

        @Nullable
        AddProgVars addProgVars;
    }

    static class ReplaceWith {

        TermOrSeq termOrSeq;
    }

    static class Add {

        Seq seq;
    }

    static class AddRules {

        List<Taclet> taclets;
    }

    static class AddProgVars {

        List<String> varIds;
    }

    static class Modifiers {

        List<String> rulesets;

        boolean nonInteractive;

        @Nullable
        String displayName;

        @Nullable
        String helpText;

        @Nullable
        Triggers triggers;
    }

    static class Triggers {

        String id;

        Term triggerTerm;

        List<Term> avoidTerms;
    }

    static class VarexpList {

        List<Varexp> varexps;
    }

    static class Varexp {

        boolean negated;

        String varExpId;

        List<String> parameters;

        List<Object> arguments;
    }

    static class Label {

        List<SingleLabel> labels;
    }

    static class SingleLabel {

        @Nullable
        String name;

        boolean isStar;

        List<String> params;
    }

    static class LocsetTerm {

        List<LocationTerm> locations;
    }

    static class LocationTerm {

        Term obj;

        Term field;
    }

    static class AccessTerm {

        @Nullable
        SortId qualifier;

        String firstName;

        @Nullable
        FormalSortArgs formalArgs;

        @Nullable
        Call call;

        List<Attribute> attributes;
    }

    static class Call {

        @Nullable
        BoundVariables boundVars;

        List<Term> args;
    }

    static class Attribute {

        enum AttrKind {

            STAR, SIMPLE, COMPLEX
        }

        AttrKind kind;

        @Nullable
        String id;

        @Nullable
        SortId sort;

        @Nullable
        Call call;

        @Nullable
        BracketTerm heap;
    }

    static class Abbreviation {

        String name;
    }

    static class IfThenElseTerm {

        Term cond;

        Term thenT;

        Term elseT;
    }

    static class IfExThenElseTerm {

        BoundVariables exVars;

        Term cond;

        Term thenT;

        Term elseT;
    }

    static class BracketTerm {

        Term primitive;

        List<BracketSuffixHeap> suffixes;

        List<Attribute> attributes;
    }

    static class BracketSuffixHeap {

        BraceSuffix braceSuffix;

        @Nullable
        BracketTerm heap;
    }

    static class BraceSuffix {

        enum SuffixKind {

            UPDATE, CALL, STAR, INDEX
        }

        SuffixKind kind;

        @Nullable
        Term target;

        @Nullable
        Term value;

        @Nullable
        String id;

        List<Term> args;

        @Nullable
        Term indexTerm;

        @Nullable
        Term rangeTo;
    }

    static class ProofScript {

        List<ProofScriptCommand> commands;
    }

    static class ProofScriptCommand {

        String cmd;

        List<ProofScriptParameter> parameters;
    }

    static class ConfigurationFile {

        List<CValue> values;
    }

    static class CKV {

        @Nullable
        String docComment;

        CKey key;

        CValue value;
    }

    @Nullable
    private Position position;

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public StubAstNodes setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public StubAstNodes(@Nullable Position position) {
        this.position = position;
    }

    public StubAstNodes() {
        this.position = null;
    }

    public StubAstNodes(StubAstNodes other) {
        this(other.position);
    }

    public final static class Builder {

        @Nullable()
        public Position position;

        public StubAstNodes build() {
            return new StubAstNodes(position);
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof StubAstNodes that))
            return false;
        return Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "StubAstNodes[position=%s]".formatted(position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(position);
    }

    public <R> R accept(org.key_project.key.ast.visitor.Visitor<R> visitor) {
        return visitor.visit(this);
    }

    public <R, A> R accept(org.key_project.key.ast.visitor.ArgVisitor<R, A> visitor, A arg) {
        return visitor.visit(this, arg);
    }

    public void accept(org.key_project.key.ast.visitor.VoidVisitor visitor) {
        visitor.visit(this);
    }
}
