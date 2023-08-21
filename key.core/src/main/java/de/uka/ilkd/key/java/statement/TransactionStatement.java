/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceData;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.rule.MatchConditions;

public class TransactionStatement extends JavaStatement {

    public static final String[] names = { "#beginJavaCardTransaction",
        "#commitJavaCardTransaction", "#finishJavaCardTransaction", "#abortJavaCardTransaction" };

    private final int type;

    public TransactionStatement(int type) {
        super();
        if (type != de.uka.ilkd.key.java.recoderext.TransactionStatement.BEGIN
                && type != de.uka.ilkd.key.java.recoderext.TransactionStatement.COMMIT
                && type != de.uka.ilkd.key.java.recoderext.TransactionStatement.FINISH
                && type != de.uka.ilkd.key.java.recoderext.TransactionStatement.ABORT) {
            throw new IllegalArgumentException("Wrong transaction statement type " + type);
        }
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
        return names[type - 1];
    }

    public boolean equals(Object o) {
        if (o instanceof TransactionStatement) {
            return ((TransactionStatement) o).type == this.type;
        }
        return false;
    }


    public MatchConditions match(SourceData source, MatchConditions conditions) {
        if (this.equals(source.getSource())) {
            source.next();
            return conditions;
        }
        return null;
    }

    public boolean equalsModRenaming(SourceElement source, NameAbstractionTable nat) {
        return this.equals(source);
    }


}
