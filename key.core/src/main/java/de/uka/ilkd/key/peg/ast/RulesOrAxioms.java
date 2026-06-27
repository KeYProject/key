/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import java.util.List;

/**
 * Represents a rule or axiom.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * rules_or_axioms: (name=rule_name (LPAREN term RPAREN)? | AXIOM) COLON formula (WHEN formula)? (RULESET simple_ident_comma_list)?;
 * }</pre>
 */
@NullMarked
public class RulesOrAxioms extends BaseAstNode {
    private final @Nullable String name;
    private final @Nullable Term condition;
    private final boolean isAxiom;
    private final Formula formula;
    private final @Nullable Formula whenCondition;
    private final List<String> rulesetNames;

    public RulesOrAxioms(Position position, @Nullable String name, @Nullable Term condition,
                         boolean isAxiom, Formula formula, @Nullable Formula whenCondition, List<String> rulesetNames) {
        super(position);
        this.name = name;
        this.condition = condition;
        this.isAxiom = isAxiom;
        this.formula = formula;
        this.whenCondition = whenCondition;
        this.rulesetNames = rulesetNames;
        if (condition != null) setChildParent(condition);
        setChildParent(formula);
        if (whenCondition != null) setChildParent(whenCondition);
    }

    public @Nullable String getName() {
        return name;
    }

    public @Nullable Term getCondition() {
        return condition;
    }

    public boolean isAxiom() {
        return isAxiom;
    }

    public Formula getFormula() {
        return formula;
    }

    public @Nullable Formula getWhenCondition() {
        return whenCondition;
    }

    public List<String> getRulesetNames() {
        return rulesetNames;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}