/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.statement;

import java.util.List;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.rule.MatchConditions;

import com.github.javaparser.ast.key.KeyTransactionStatement;

public class TransactionStatement extends JavaStatement {
    private final KeyTransactionStatement.TransactionType type;

    public TransactionStatement(KeyTransactionStatement.TransactionType type) {
        super();
        this.type = type;
    }

    public TransactionStatement(
            PositionInfo pi, List<Comment> c,
            KeyTransactionStatement.TransactionType type) {
        super(pi, c);
        this.type = type;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnTransactionStatement(this);
    }

    @Override
    public ProgramElement getChildAt(int index) {
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

    public MatchConditions match(SourceData source, MatchConditions conditions) {
        if (this.equals(source.getSource())) {
            source.next();
            return conditions;
        }
        return null;
    }
}
