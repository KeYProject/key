/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.builder;


import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.NamespaceSet;
import org.key_project.rusty.logic.Semisequent;
import org.key_project.rusty.logic.Sequent;
import org.key_project.rusty.logic.SequentFormula;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.sv.ModalOperatorSV;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.parser.KeYRustyParser;
import org.key_project.util.collection.ImmutableSet;

public class ExpressionBuilder extends DefaultBuilder {
    public ExpressionBuilder(Services services, NamespaceSet nss) {
        super(services, nss);
    }

    protected ImmutableSet<Modality.RustyModalityKind> opSVHelper(String opName, ImmutableSet<Modality.RustyModalityKind> modalityKinds) {
        if (opName.charAt(0) == '#') {
            return lookupOperatorSV(opName, modalityKinds);
        } else {
            Modality.RustyModalityKind m = Modality.RustyModalityKind.getKind(opName);
            if (m == null) {
                semanticError(null, "Unrecognised operator: " + opName);
            }
            modalityKinds = modalityKinds.add(m);
        }
        return modalityKinds;
    }

    @Override
    public Sequent visitSeq(KeYRustyParser.SeqContext ctx) {
        Semisequent ant = accept(ctx.ant);
        Semisequent suc = accept(ctx.suc);
        return Sequent.createSequent(ant, suc);
    }

    @Override
    public Sequent visitSeqEOF(KeYRustyParser.SeqEOFContext ctx) {
        return accept(ctx.seq());
    }


//    @Override
//    public Semisequent visitSemisequent(KeYRustyParser.SemisequentContext ctx) {
//        Semisequent ss = accept(ctx.ss);
//        if (ss == null) {
//            ss = Semisequent.EMPTY_SEMISEQUENT;
//        }
//        Term head = accept(ctx.term());
//        if (head != null) {
//            ss = ss.insertFirst(new SequentFormula(head)).semisequent();
//        }
//        return ss;
//    }
    
    private ImmutableSet<Modality.RustyModalityKind> lookupOperatorSV(String opName,
                                                                     ImmutableSet<Modality.RustyModalityKind> modalityKinds) {
        SchemaVariable sv = schemaVariables().lookup(new Name(opName));
        if (sv instanceof ModalOperatorSV osv) {
            modalityKinds = modalityKinds.union(osv.getModalities());
        } else {
            semanticError(null, "Schema variable " + opName + " not defined.");
        }
        return modalityKinds;
    }
}
