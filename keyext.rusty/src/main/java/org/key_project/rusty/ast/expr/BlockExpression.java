/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import java.util.ArrayList;
import java.util.Objects;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.ElseBranch;
import org.key_project.rusty.ast.ProgramPrefixUtil;
import org.key_project.rusty.ast.abstraction.TupleType;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.stmt.Statement;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.rusty.logic.PosInProgram;
import org.key_project.rusty.logic.PossibleProgramPrefix;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;

public class BlockExpression implements Expr, PossibleProgramPrefix, ThenBranch, ElseBranch {
    protected final ImmutableList<Statement> statements;
    protected final Expr value;
    private final int prefixLength;

    public BlockExpression(ImmutableList<Statement> statements, Expr value) {
        this.statements = statements;
        this.value = value;
        ProgramPrefixUtil.ProgramPrefixInfo info = ProgramPrefixUtil.computeEssentials(this);
        prefixLength = info.length();
    }

    public BlockExpression(ExtList children) {
        statements = ImmutableList.of(children.collect(Statement.class));
        value = children.get(Expr.class);
        ProgramPrefixUtil.ProgramPrefixInfo info = ProgramPrefixUtil.computeEssentials(this);
        prefixLength = info.length();
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (0 <= n && n < statements.size())
            return Objects.requireNonNull(statements.get(n));
        if (n == statements.size())
            return value;
        throw new IndexOutOfBoundsException("BlockExpression has less than " + n + " children");
    }

    @Override
    public int getChildCount() {
        return statements.size() + (value == null ? 0 : 1);
    }

    public ImmutableList<Statement> getStatements() {
        return statements;
    }

    public Expr getValue() {
        return value;
    }

    @Override
    public String toString() {
        var sb = new StringBuilder();
        sb.append("{\n");
        for (var s : statements) {
            sb.append("\t");
            sb.append(s.toString());
            sb.append("\n");
        }
        if (value != null) {
            sb.append("\t");
            sb.append(value);
            sb.append("\n");
        }
        sb.append("}");
        return sb.toString();
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == this) {
            return true;
        }
        if (obj == null || obj.getClass() != this.getClass()) {
            return false;
        }
        final var other = (BlockExpression) obj;
        if (value == null && other.value != null || value != null && !value.equals(other.value)) {
            return false;
        }
        return statements.equals(other.statements) && prefixLength == other.prefixLength;
    }

    @Override
    public int hashCode() {
        int hashcode = 5;
        hashcode = 31 * hashcode + statements.hashCode();
        hashcode = 31 * hashcode + (value == null ? 0 : value.hashCode());
        hashcode = 31 * hashcode + prefixLength;
        return hashcode;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnBlockExpression(this);
    }

    @Override
    public boolean isPrefix() {
        return getChildCount() != 0;
    }

    @Override
    public boolean hasNextPrefixElement() {
        return getChildCount() != 0 && getChild(0) instanceof PossibleProgramPrefix;
    }

    @Override
    public PossibleProgramPrefix getNextPrefixElement() {
        if (hasNextPrefixElement()) {
            return (PossibleProgramPrefix) getChild(0);
        }
        throw new IndexOutOfBoundsException("No next prefix element " + this);
    }

    @Override
    public PossibleProgramPrefix getLastPrefixElement() {
        return hasNextPrefixElement() ? getNextPrefixElement().getLastPrefixElement() : this;
    }

    @Override
    public ImmutableArray<PossibleProgramPrefix> getPrefixElements() {
        return computePrefixElements(this);
    }

    @Override
    public PosInProgram getFirstActiveChildPos() {
        return PosInProgram.ZERO;
    }

    @Override
    public int getPrefixLength() {
        return prefixLength;
    }

    /** computes the prefix elements for the given array of statment block */
    public static ImmutableArray<PossibleProgramPrefix> computePrefixElements(
            PossibleProgramPrefix current) {
        final ArrayList<PossibleProgramPrefix> prefix = new ArrayList<>();
        prefix.add(current);

        while (current.hasNextPrefixElement()) {
            current = current.getNextPrefixElement();
            prefix.add(current);
        }

        return new ImmutableArray<>(prefix);
    }

    @Override
    public Type type(Services services) {
        return value == null ? TupleType.UNIT : value.type(services);
    }
}
