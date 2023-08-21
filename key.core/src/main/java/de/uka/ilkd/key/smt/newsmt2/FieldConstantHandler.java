/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.util.Map;
import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

import org.key_project.util.collection.ImmutableArray;

/**
 * This SMT translation handler takes care of field constants.
 *
 * Field constants have a name that follows the scheme {@code ClassName::$fieldName}. This handler
 * treats any unique function symbol of sort {@code Field} that follows this scheme as a function
 * constant.
 *
 * It is made sure that different symbols do not map to the field entity.
 *
 * To this end a function fieldIdentifier is used and an assertion like the following is added which
 * states for C::$f (assert (= (fieldIdentifier |field_C::$f|) -42)
 *
 * Each function symbol gets a new unique negative integer. Positive integers are kept for the arr()
 * function to make sure that is an injection.
 *
 * The integer constants are obtained via a counter stored in the state. The key is
 * {@link #CONSTANT_COUNTER_PROPERTY}.
 *
 * TODO It seems that this could be extended to a general "UniqueHandler" if required.
 *
 * @author Mattias Ulbrich
 */
public class FieldConstantHandler implements SMTHandler {

    private static final String CONSTANT_COUNTER_PROPERTY = "fieldConstant.counter";
    private static final ImmutableArray<Term> NO_ARGS = new ImmutableArray<>();
    private Services services;

    @Override
    public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets,
            String[] handlerOptions) {
        this.services = services;
        masterHandler.addDeclarationsAndAxioms(handlerSnippets);
    }

    @Override
    public boolean canHandle(Operator op) {
        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        return op.arity() == 0 && op.sort(NO_ARGS) == heapLDT.getFieldSort()
                && op instanceof Function && ((Function) op).isUnique()
                && (op.name().toString().contains("::$") || op.name().toString().contains("::<"))
                || op == heapLDT.getArr();
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        String name = term.op().name().toString();
        String smtName = "field_" + name;

        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        Operator op = term.op();

        if (op == heapLDT.getArr()) {
            trans.introduceSymbol("arr");
            return trans.handleAsFunctionCall("arr", term);
        }

        if (!trans.isKnownSymbol(smtName)) {
            Map<String, Object> state = trans.getTranslationState();
            Integer curVal = (Integer) state.getOrDefault(CONSTANT_COUNTER_PROPERTY, 2);

            trans.introduceSymbol("fieldIdentifier");

            trans.addDeclaration(new SExpr("declare-const", smtName, "U"));

            trans.addAxiom(HandlerUtil.funTypeAxiom((SortedOperator) op, smtName, trans));

            trans.addAxiom(new SExpr("assert", new SExpr("=", new SExpr("fieldIdentifier", smtName),
                new SExpr("-", IntegerOpHandler.INT, curVal.toString()))));

            state.put(CONSTANT_COUNTER_PROPERTY, curVal + 1);
            trans.addKnownSymbol(smtName);
        }

        return new SExpr(smtName, Type.UNIVERSE);
    }

}
