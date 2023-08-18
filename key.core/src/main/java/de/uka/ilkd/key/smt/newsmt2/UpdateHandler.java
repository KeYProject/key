/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.util.ArrayList;
import java.util.List;
import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

/**
 * This handler treats KeY updated terms ({x:=5}x>4).
 *
 * Updates are replaced by let-expressions.
 */
public class UpdateHandler implements SMTHandler {

    private Services services;

    @Override
    public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets,
            String[] handlerOptions) {
        this.services = services;
    }

    @Override
    public boolean canHandle(Operator op) {
        return op == UpdateApplication.UPDATE_APPLICATION;
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) {

        Term update = term.sub(0);
        assert update.sort() == Sort.UPDATE;

        List<SExpr> individualUpdates = new ArrayList<>();
        collectUpdates(update, individualUpdates, trans);

        Term inner = term.sub(1);
        SExpr innerSMT = trans.translate(inner);
        return new SExpr("let", innerSMT.getType(), new SExpr(individualUpdates), innerSMT);
    }

    private void collectUpdates(Term update, List<SExpr> individualUpdates, MasterHandler trans) {
        if (update.op() == UpdateJunctor.PARALLEL_UPDATE) {
            for (Term subUpd : update.subs()) {
                collectUpdates(subUpd, individualUpdates, trans);
            }
        } else if (update.op() == UpdateJunctor.SKIP) {
            // Do precisely that: skip
        } else if (update.op() instanceof ElementaryUpdate) {
            ElementaryUpdate elemUpd = (ElementaryUpdate) update.op();
            Term target = services.getTermFactory().createTerm(elemUpd.lhs());
            SExpr smtTarget = trans.translate(target);
            SExpr smtValue = trans.translate(update.sub(0), Type.UNIVERSE);
            individualUpdates.add(new SExpr(smtTarget, smtValue));
        } else {
            throw new RuntimeException("Unexpected update connector " + update);
        }
    }

}
