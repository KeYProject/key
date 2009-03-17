// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.jmltest;

/**
 * @author mbender@uni-koblenz.de
 */

import java.io.IOException;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.CastFunctionSymbol;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.init.SpecExtPO;
import de.uka.ilkd.key.util.pp.Layouter;
import de.uka.ilkd.key.util.pp.StringBackend;

public class JMLLogicPrinter extends LogicPrinter {

    public static final int DLW = 100000;

    private SpecExtPO po;

    public JMLLogicPrinter(ProgramPrinter pgr, NotationInfo notaInfo,
            Services serv, SpecExtPO po) {
        super(pgr, notaInfo, serv, true);
        this.po = po;
        lineWidth = DLW;
        backend = new StringBackend(DLW);
        layouter = new Layouter(backend, 0);

        // pure = true;
        // backend = new PosTableStringBackend(5000);
        // layouter = new Layouter(backend, 100);
        // this.notaInfo = notaInfo;
        // prgPrinter = new JMLProgPrinter(true, true);
    }

    public void printIfThenElseTerm(Term t, String keyword) throws IOException {
        startTerm(t.arity());
        layouter.beginC(0);
        layouter.print(keyword);
        if (t.varsBoundHere(0).size() > 0) {
//            layouter.print(" ");
            printVariables(t.varsBoundHere(0));
        }
//        layouter.print(" ");
        markStartSub();
        printTerm(t.sub(0));
        markEndSub();
//        layouter.print(" ");
        for (int i = 1; i < t.arity(); ++i) {
            layouter.brk(1, 3);
            if (i == 1) {
                layouter.print("? ");
            } else {
                layouter.print(": ");
            }
            markStartSub();
            printTerm(t.sub(i));
            markEndSub();
//            layouter.print(" ");
        }
        layouter.print(")");
        layouter.end();
    }

    public void printPrefixTerm(String name, Term t, int ass)
            throws IOException {
        startTerm(1);
        layouter.print(name);
        layouter.print("(");
        maybeParens(t, ass);
        layouter.print(")");
    }

    public void printQuantifierTerm(String name,
            ArrayOfQuantifiableVariable vars, Term phi, int ass)
            throws IOException {
        layouter.beginC(2);
        layouter.print("(");
        layouter.print(name).print(" ");
        printVariables(vars);
        layouter.print("true;");
        layouter.brk();
        startTerm(1);
        maybeParens(phi, ass);
        layouter.print(")");
        layouter.end();
    }

    public void printFunctionTerm(String name, Term t) throws IOException {
        startTerm(t.arity());

        LogicVariable selfLogic = po.getSelfVarAsLogicVar();
        ProgramVariable selfProg = po.getSelfVarAsProgVar();
        ProgramVariable result = po.getResult();
        if (((selfLogic != null) && (t.op().toString().equals(selfLogic
                .toString())))
                || ((selfProg != null) && t.op().toString().equals(
                        selfProg.toString()))) {
            layouter.print("this");
        } else if ((result != null)
                && (t.op().toString().equals(result.toString()))) {
            layouter.print("\\result");
        } else if (name.equals("TRUE")) {
            layouter.print("true");
        } else if (name.equals("FALSE")) {
            layouter.print("false");
        } else {
            layouter.print(name);
        }

        if (t.arity() > 0 || t.op() instanceof ProgramMethod) {
            layouter.print("(").beginC(0);
            for (int i = 0; i < t.arity(); i++) {
                markStartSub();
                printTerm(t.sub(i));
                markEndSub();
                if (i < t.arity() - 1) {
                    layouter.print(",").brk(1, 0);
                }
            }
            layouter.print(")").end();
        }
    }

    public void printCast(String pre, String post, Term t, int ass)
            throws IOException {
        final CastFunctionSymbol cast = (CastFunctionSymbol) t.op();
        startTerm(t.arity());
        layouter.print(pre);
        layouter.print((services.getTypeConverter().getModelFor(
                cast.getSortDependingOn()).javaType()).toString());
        layouter.print(post);
        maybeParens(t.sub(0), ass);
    }

    public StringBuffer result() {
        try {
            layouter.flush();
        } catch (IOException e) {
            throw new RuntimeException("IO Exception in pretty printer:\n" + e);
        }
        return new StringBuffer(((StringBackend) backend).getString());
    }

}
