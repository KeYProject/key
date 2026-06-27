/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import java.util.ArrayList;
import java.util.List;

/**
 * Represents a taclet (KeY's rule specification language).
 * Corresponds to the grammar rule: taclet
 *
 * @author Cline
 * @version 1.0
 */
@NullMarked
public class Taclet extends BaseAstNode implements Declaration {
    private final @Nullable String docComment;
    private final boolean isLemma;
    private final String name;
    private final @Nullable OptionList options;
    private final List<SchemaVarDecl> schemaVars;
    private final @Nullable Seq assumes;
    private final @Nullable TermOrSeq find;
    private final List<String> findModifiers;
    private final List<VarexpList> varConds;
    private final GoalSpecs goalSpecs;
    private final Modifiers modifiers;

    public Taclet(Position position,
                  @Nullable String docComment, boolean isLemma, String name,
                  @Nullable OptionList options, List<SchemaVarDecl> schemaVars,
                  @Nullable Seq assumes, @Nullable TermOrSeq find,
                  List<String> findModifiers, List<VarexpList> varConds,
                  GoalSpecs goalSpecs, Modifiers modifiers) {
        super(position);
        this.docComment = docComment;
        this.isLemma = isLemma;
        this.name = name;
        this.options = options;
        this.schemaVars = schemaVars;
        this.assumes = assumes;
        this.find = find;
        this.findModifiers = findModifiers;
        this.varConds = varConds;
        this.goalSpecs = goalSpecs;
        this.modifiers = modifiers;

        setChildParent(options);
        for (SchemaVarDecl sv : schemaVars) {
            setChildParent(sv);
        }
        setChildParent(assumes);
        setChildParent(find);
        setChildParent(goalSpecs);
        setChildParent(modifiers);
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    public @Nullable String getDocComment() {
        return docComment;
    }

    public boolean isLemma() {
        return isLemma;
    }

    public String getName() {
        return name;
    }

    public @Nullable OptionList getOptions() {
        return options;
    }

    public List<SchemaVarDecl> getSchemaVars() {
        return schemaVars;
    }

    public @Nullable Seq getAssumes() {
        return assumes;
    }

    public @Nullable TermOrSeq getFind() {
        return find;
    }

    public List<String> getFindModifiers() {
        return findModifiers;
    }

    public List<VarexpList> getVarConds() {
        return varConds;
    }

    public GoalSpecs getGoalSpecs() {
        return goalSpecs;
    }

    public Modifiers getModifiers() {
        return modifiers;
    }
}