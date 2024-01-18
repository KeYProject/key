/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.rule.metaconstruct.IntroAtPreDefsOp;
import de.uka.ilkd.key.speclang.TermReplacementMap;
import de.uka.ilkd.key.speclang.jml.translation.ProgramVariableCollection;
import de.uka.ilkd.key.speclang.njml.JmlParser;

import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;
import org.key_project.util.ExtList;

import java.util.Map;

/**
 * JML set statement
 *
 * @author Julian Wiesler
 */
public class SetStatement extends JavaStatement {
    /**
     * The parser context of the statement produced during parsing.
     */
    private final JmlParser.Set_statementContext context;
    private final Services services;

    /**
     * The target of the assignment as a term. Either a heap access for a ghost field
     * or a ghost variable.
     */
    private Term target;

    /**
     * The value of the assignment as a term.
     */
    private Term value;

    private ProgramVariableCollection vars;

    /** Constructor used in recoderext */
    public SetStatement(JmlParser.Set_statementContext context, PositionInfo positionInfo, Services services) {
        super(positionInfo);
        this.context = context;
        this.services = services;
    }

    /** Constructor used when cloning */
    public SetStatement(SetStatement copyFrom) {
        this.value = copyFrom.value;
        this.target = copyFrom.target;
        this.context = copyFrom.context;
        this.services = copyFrom.services;
    }

    /**
     * Removes the attached parser context from this set statement
     *
     * @return the parser context that was attached
     */
    public JmlParser.Set_statementContext getParserContext() {
        return context;
    }

    public void setTranslated(Term target, Term value, ProgramVariableCollection pv) {
        assert target == null : "The translation has already been set on this statement.";
        this.target = target;
        this.value = value;
        this.vars = pv;
    }

    public Term getTarget(final Term self) {
        final TermFactory termFactory = services.getTermFactory();
        final TermReplacementMap replacementMap = new TermReplacementMap(termFactory);
        if (self != null) {
            replacementMap.replaceSelf(vars.selfVar, self, services);
        }
        replacementMap.replaceRemembranceLocalVariables(vars.atPreVars, vars.atPres, services);
        replacementMap.replaceRemembranceLocalVariables(vars.atBeforeVars, vars.atBefores,
                services);
        final OpReplacer replacer =
                new OpReplacer(replacementMap, termFactory, services.getProof());
        return replacer.replace(target);
    }

    public Term getValue(final Term self) {
        final TermFactory termFactory = services.getTermFactory();
        final TermReplacementMap replacementMap = new TermReplacementMap(termFactory);
        if (self != null) {
            replacementMap.replaceSelf(vars.selfVar, self, services);
        }
        replacementMap.replaceRemembranceLocalVariables(vars.atPreVars, vars.atPres, services);
        replacementMap.replaceRemembranceLocalVariables(vars.atBeforeVars, vars.atBefores,
                services);
        final OpReplacer replacer =
                new OpReplacer(replacementMap, termFactory, services.getProof());
        return replacer.replace(value);
    }

    /**
     * updates this statement with prestate renaming
     *
     * @param atPres prestate renaming
     * @param services services
     */
    public void updateVars(final Map<LocationVariable, Term> atPres, final Services services) {
        final TermFactory termFactory = services.getTermFactory();
        final TermReplacementMap replacementMap = new TermReplacementMap(termFactory);
        replacementMap.replaceRemembranceLocalVariables(vars.atPreVars, atPres, services);
        final OpReplacer replacer = new OpReplacer(replacementMap, termFactory, services.getProof());
        this.target = replacer.replace(target);
        this.value = replacer.replace(value);
        vars.atPres = atPres;
    }

    /** {@inheritDoc} */
    @Override
    public void visit(Visitor v) {
        v.performActionOnSetStatement(this);
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        throw new IndexOutOfBoundsException("SetStatement has no program children");
    }

    public Term getTarget() {
        return target;
    }

    public Term getValue() {
        return value;
    }

    public ProgramVariableCollection getVars() {
        return vars;
    }
}
