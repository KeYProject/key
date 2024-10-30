/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import java.util.ArrayList;
import java.util.Objects;
import java.util.stream.Collectors;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.ElseBranch;
import org.key_project.rusty.ast.ProgramPrefixUtil;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.stmt.Statement;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.rusty.logic.PosInProgram;
import org.key_project.rusty.logic.ProgramPrefix;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;

public class BlockExpression implements Expr, ProgramPrefix, ThenBranch, ElseBranch {
    protected final ImmutableList<Statement> statements;
    protected final Expr value;
    private final int prefixLength;

    public BlockExpression(ImmutableList<Statement> statements, Expr value) {
        this.statements = statements;
        this.value = value;
        ProgramPrefixUtil.ProgramPrefixInfo info = ProgramPrefixUtil.computeEssentials(this);
        prefixLength = info.getLength();
    }

    public BlockExpression(ExtList children) {
        statements = ImmutableList.of(children.collect(Statement.class));
        value = children.get(Expr.class);
        ProgramPrefixUtil.ProgramPrefixInfo info = ProgramPrefixUtil.computeEssentials(this);
        prefixLength = info.getLength();
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
        return statements.size() + 1;
    }

    public ImmutableList<Statement> getStatements() {
        return statements;
    }

    public Expr getValue() {
        return value;
    }

    @Override
    public String toString() {
        return "{\n"
            + statements.stream().map(s -> "\t" + s.toString()).collect(Collectors.joining("\n"))
            + "\n\t" + value.toString()
            + "\n}";
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
    public boolean hasNextPrefixElement() {
        return getChildCount() != 0 && getChild(0) instanceof ProgramPrefix;
    }

    @Override
    public ProgramPrefix getNextPrefixElement() {
        if (hasNextPrefixElement()) {
            return (ProgramPrefix) getChild(0);
        }
        throw new IndexOutOfBoundsException("No next prefix element " + this);
    }

    @Override
    public ProgramPrefix getLastPrefixElement() {
        return hasNextPrefixElement() ? getNextPrefixElement().getLastPrefixElement() : this;
    }

    @Override
    public ImmutableArray<ProgramPrefix> getPrefixElements() {
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
    public static ImmutableArray<ProgramPrefix> computePrefixElements(
            ProgramPrefix current) {
        final ArrayList<ProgramPrefix> prefix = new ArrayList<>();
        prefix.add(current);

        while (current.hasNextPrefixElement()) {
            current = current.getNextPrefixElement();
            prefix.add(current);
        }

        return new ImmutableArray<>(prefix);
    }

    @Override
    public Type type(Services services) {
        return value.type(services);
    }
}
