package org.key_project.key.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import java.util.*;

@NullMarked()
public final class OneSchemaVarDecl extends BaseAstNode {

    enum Kind {

        MODAL_OPERATOR,
        PROGRAM,
        FORMULA,
        TERMLABEL,
        UPDATE,
        SKOLEM_FORMULA,
        TERM,
        VARIABLES,
        VARIABLE,
        SKOLEM_TERM
    }

    private Kind kind;

    @Nullable
    private SchemaModifiers modifiers;

    @Nullable
    private SortId sortId;

    @Nullable
    private String nameString;

    @Nullable
    private SimpleIdentDots parameter;

    private List<String> identifiers;

    @Nullable
    private String modalOpName;

    @Nullable
    private SortId modalOpSort;

    @Nullable
    private Position position;

    public Kind kind() {
        return kind;
    }

    public OneSchemaVarDecl setKind(Kind value) {
        kind = value;
        return this;
    }

    @Nullable()
    public SchemaModifiers modifiers() {
        return modifiers;
    }

    public OneSchemaVarDecl setModifiers(@Nullable() SchemaModifiers value) {
        modifiers = value;
        return this;
    }

    @Nullable()
    public SortId sortId() {
        return sortId;
    }

    public OneSchemaVarDecl setSortId(@Nullable() SortId value) {
        sortId = value;
        return this;
    }

    @Nullable()
    public String nameString() {
        return nameString;
    }

    public OneSchemaVarDecl setNameString(@Nullable() String value) {
        nameString = value;
        return this;
    }

    @Nullable()
    public SimpleIdentDots parameter() {
        return parameter;
    }

    public OneSchemaVarDecl setParameter(@Nullable() SimpleIdentDots value) {
        parameter = value;
        return this;
    }

    public List<String> identifiers() {
        return identifiers;
    }

    public OneSchemaVarDecl setIdentifiers(List<String> value) {
        identifiers = value;
        return this;
    }

    @Nullable()
    public String modalOpName() {
        return modalOpName;
    }

    public OneSchemaVarDecl setModalOpName(@Nullable() String value) {
        modalOpName = value;
        return this;
    }

    @Nullable()
    public SortId modalOpSort() {
        return modalOpSort;
    }

    public OneSchemaVarDecl setModalOpSort(@Nullable() SortId value) {
        modalOpSort = value;
        return this;
    }

    @Nullable()
    @java.lang.Override()
    public Position position() {
        return position;
    }

    @java.lang.Override()
    public OneSchemaVarDecl setPosition(@Nullable() Position value) {
        position = value;
        return this;
    }

    public OneSchemaVarDecl(Kind kind, @Nullable SchemaModifiers modifiers, @Nullable SortId sortId, @Nullable String nameString, @Nullable SimpleIdentDots parameter, List<String> identifiers, @Nullable String modalOpName, @Nullable SortId modalOpSort, @Nullable Position position) {
        this.kind = Objects.requireNonNull(kind);
        this.modifiers = modifiers;
        this.sortId = sortId;
        this.nameString = nameString;
        this.parameter = parameter;
        this.identifiers = Objects.requireNonNull(identifiers);
        this.modalOpName = modalOpName;
        this.modalOpSort = modalOpSort;
        this.position = position;
    }

    public OneSchemaVarDecl(Kind kind, List<String> identifiers) {
        this.kind = Objects.requireNonNull(kind);
        this.modifiers = null;
        this.sortId = null;
        this.nameString = null;
        this.parameter = null;
        this.identifiers = Objects.requireNonNull(identifiers);
        this.modalOpName = null;
        this.modalOpSort = null;
        this.position = null;
    }

    public OneSchemaVarDecl(OneSchemaVarDecl other) {
        this(other.kind, other.modifiers, other.sortId, other.nameString, other.parameter, other.identifiers, other.modalOpName, other.modalOpSort, other.position);
    }

    public final static class Builder {

        @Nullable()
        public Kind kind;

        @Nullable()
        public SchemaModifiers modifiers;

        @Nullable()
        public SortId sortId;

        @Nullable()
        public String nameString;

        @Nullable()
        public SimpleIdentDots parameter;

        @Nullable()
        public List<String> identifiers;

        @Nullable()
        public String modalOpName;

        @Nullable()
        public SortId modalOpSort;

        @Nullable()
        public Position position;

        public OneSchemaVarDecl build() {
            return new OneSchemaVarDecl(kind, modifiers, sortId, nameString, parameter, identifiers, modalOpName, modalOpSort, position);
        }

        public Builder kind(Kind kind) {
            this.kind = kind;
            return this;
        }

        public Builder modifiers(SchemaModifiers modifiers) {
            this.modifiers = modifiers;
            return this;
        }

        public Builder sortId(SortId sortId) {
            this.sortId = sortId;
            return this;
        }

        public Builder nameString(String nameString) {
            this.nameString = nameString;
            return this;
        }

        public Builder parameter(SimpleIdentDots parameter) {
            this.parameter = parameter;
            return this;
        }

        public Builder identifiers(List<String> identifiers) {
            this.identifiers = identifiers;
            return this;
        }

        public Builder modalOpName(String modalOpName) {
            this.modalOpName = modalOpName;
            return this;
        }

        public Builder modalOpSort(SortId modalOpSort) {
            this.modalOpSort = modalOpSort;
            return this;
        }

        public Builder position(Position position) {
            this.position = position;
            return this;
        }

        public Builder identifiers(String identifiers) {
            if (this.identifiers == null)
                this.identifiers = new ArrayList<>();
            this.identifiers.add(identifiers);
            return this;
        }
    }

    public Builder builder() {
        Builder b = new Builder();
        b.kind = kind;
        b.modifiers = modifiers;
        b.sortId = sortId;
        b.nameString = nameString;
        b.parameter = parameter;
        b.identifiers = identifiers;
        b.modalOpName = modalOpName;
        b.modalOpSort = modalOpSort;
        b.position = position;
        return b;
    }

    @Override()
    public boolean equals(java.lang.Object o) {
        if (this == o)
            return true;
        if (!(o instanceof OneSchemaVarDecl that))
            return false;
        return Objects.equals(kind, that.kind) && Objects.equals(modifiers, that.modifiers) && Objects.equals(sortId, that.sortId) && Objects.equals(nameString, that.nameString) && Objects.equals(parameter, that.parameter) && Objects.equals(identifiers, that.identifiers) && Objects.equals(modalOpName, that.modalOpName) && Objects.equals(modalOpSort, that.modalOpSort) && Objects.equals(position, that.position);
    }

    @Override()
    public String toString() {
        return "OneSchemaVarDecl[kind=%s, modifiers=%s, sortId=%s, nameString=%s, parameter=%s, identifiers=%s, modalOpName=%s, modalOpSort=%s, position=%s]".formatted(kind, modifiers, sortId, nameString, parameter, identifiers, modalOpName, modalOpSort, position);
    }

    @Override()
    public int hashCode() {
        return Objects.hash(kind, modifiers, sortId, nameString, parameter, identifiers, modalOpName, modalOpSort, position);
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
