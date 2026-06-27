/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import java.util.List;

/**
 * Represents a single schema variable declaration.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * one_schema_var_decl: MODALOPERATOR ... | PROGRAM ... | FORMULA ... | TERMLABEL ... | UPDATE ... | SKOLEMFORMULA ... | (TERM | VARIABLES | VARIABLE | SKOLEMTERM) ...;
 * }</pre>
 */
@NullMarked
public class OneSchemaVarDecl extends BaseAstNode {
    public enum Kind {
        MODAL_OPERATOR, PROGRAM, FORMULA, TERMLABEL, UPDATE, SKOLEM_FORMULA, TERM, VARIABLES, VARIABLE, SKOLEM_TERM
    }

    private final Kind kind;
    private final @Nullable SchemaModifiers modifiers;
    private final @Nullable SortId sortId;
    private final @Nullable String nameString;
    private final @Nullable SimpleIdentDots parameter;
    private final List<String> identifiers;
    private final @Nullable String modalOpName;
    private final @Nullable SortId modalOpSort;

    public OneSchemaVarDecl(Position position, Kind kind, @Nullable SchemaModifiers modifiers,
                            @Nullable SortId sortId, List<String> identifiers) {
        super(position);
        this.kind = kind;
        this.modifiers = modifiers;
        this.sortId = sortId;
        this.identifiers = identifiers;
        this.nameString = null;
        this.parameter = null;
        this.modalOpName = null;
        this.modalOpSort = null;
        if (modifiers != null) setChildParent(modifiers);
        if (sortId != null) setChildParent(sortId);
    }

    public OneSchemaVarDecl(Position position, Kind kind, @Nullable SchemaModifiers modifiers,
                            String nameString, SimpleIdentDots parameter, List<String> identifiers) {
        super(position);
        this.kind = kind;
        this.modifiers = modifiers;
        this.nameString = nameString;
        this.parameter = parameter;
        this.identifiers = identifiers;
        this.sortId = null;
        this.modalOpName = null;
        this.modalOpSort = null;
        if (modifiers != null) setChildParent(modifiers);
        if (parameter != null) setChildParent(parameter);
    }

    public OneSchemaVarDecl(Position position, Kind kind, @Nullable SchemaModifiers modifiers,
                            @Nullable SortId modalOpSort, List<String> modalOpNames, String name) {
        super(position);
        this.kind = kind;
        this.modifiers = modifiers;
        this.modalOpSort = modalOpSort;
        this.modalOpName = name;
        this.identifiers = modalOpNames;
        this.sortId = null;
        this.nameString = null;
        this.parameter = null;
        if (modifiers != null) setChildParent(modifiers);
        if (modalOpSort != null) setChildParent(modalOpSort);
    }

    public Kind getKind() {
        return kind;
    }

    public @Nullable SchemaModifiers getModifiers() {
        return modifiers;
    }

    public @Nullable SortId getSortId() {
        return sortId;
    }

    public List<String> getIdentifiers() {
        return identifiers;
    }

    public @Nullable String getNameString() {
        return nameString;
    }

    public @Nullable SimpleIdentDots getParameter() {
        return parameter;
    }

    public @Nullable String getModalOpName() {
        return modalOpName;
    }

    public @Nullable SortId getModalOpSort() {
        return modalOpSort;
    }
}