/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.ast.expression.literal;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.rule.MatchConditions;
import org.jspecify.annotations.Nullable;
import org.key_project.logic.Name;

import java.util.List;

/**
 * Literal.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract sealed

class Literal extends JavaProgramElement
        implements Expression, TerminalProgramElement
permits AbstractIntegerLiteral, BooleanLiteral, DoubleLiteral, EmptyMapLiteral,
        EmptySeqLiteral, EmptySetLiteral, FloatLiteral, FreeLiteral, NullLiteral, RealLiteral, StringLiteral
{
    public Literal(@Nullable PositionInfo pi, @Nullable List<Comment> comments) {
        super(pi, comments);
    }

    public Literal() {
        super();
    }

    /**
     * retrieves the literal's type (as it is independant of the
     * execution context, it is same as using {@link #getKeYJavaType(Services)})
     *
     * @param javaServ
     *        the Services offering access to the Java model
     * @param ec
     *        the ExecutionContext in which the expression is evaluated
     * @return the literal's type
     */
    @Override
    public KeYJavaType getKeYJavaType(Services javaServ,
            ExecutionContext ec) {
        return getKeYJavaType(javaServ);
    }

    /**
     * retrieves the literal's type
     *
     * @param javaServ
     *        the Services offering access to the Java model
     * @return the literal's type
     */
    public abstract KeYJavaType getKeYJavaType(Services javaServ);


    @Override
    public MatchConditions match(SourceData source, MatchConditions matchCond) {
        final ProgramElement src = source.getSource();
        if (this.equals(src)) {
            source.next();
            return matchCond;
        }
        return null;
    }

    /*
     * Return the Name of the LDT, which this Literal belongs to.
     */
    public abstract Name getLDTName();

}
