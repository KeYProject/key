/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.statement;

import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.SourceData;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.rule.MatchConditions;

import com.github.javaparser.ast.key.KeyTransactionStmt;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
public class TransactionStatement extends JavaStatement {
    private final KeyTransactionStmt.TransactionType type;

    public TransactionStatement(KeyTransactionStmt.TransactionType type) {
        super();
        this.type = type;
    }

    public TransactionStatement(
            PositionInfo pi, List<Comment> c,
            KeyTransactionStmt.TransactionType type) {
        super(pi, c);
        this.type = type;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnTransactionStatement(this);
    }

    // a transaction statement has no program children (getChildCount() is 0); the base contract
    // NonTerminalProgramElement.getChildAt(int) is over-narrow; honest @Nullable override per
    // SuperArrayDeclaration precedent (wave 7).
    @SuppressWarnings("NullAway")
    @Override
    public @Nullable ProgramElement getChildAt(int index) {
        return null;
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    public int getPrecedence() {
        return 13;
    }

    public String toString() {
        return type.symbol;
    }

    @Override
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        }
        if (o == null || o.getClass() != this.getClass()) {
            return false;
        }
        return ((TransactionStatement) o).type == this.type;
    }

    public @Nullable MatchConditions match(SourceData source,
            @Nullable MatchConditions conditions) {
        if (Objects.equals(this, source.getSource())) {
            source.next();
            return conditions;
        }
        return null;
    }
}
